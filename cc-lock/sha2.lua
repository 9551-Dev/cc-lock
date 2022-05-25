--------------------------------------------------------------------------------------------------------------------------
-- sha2.lua
--------------------------------------------------------------------------------------------------------------------------
-- VERSION: 9 (2020-05-10)
-- AUTHOR:  Egor Skriptunoff
-- LICENSE: MIT (the same license as Lua itself)
--
--
-- DESCRIPTION:
--    This module contains functions to calculate SHA digest:
--       MD5, SHA-1,
--       SHA-224, SHA-256, SHA-512/224, SHA-512/256, SHA-384, SHA-512,
--       SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128, SHAKE256,
--       HMAC
--    Written in pure Lua.
--    Compatible with:
--       Lua 5.1, Lua 5.2, Lua 5.3, Lua 5.4, Fengari, LuaJIT 2.0/2.1 (any CPU endianness).
--    Main feature of this module: it was heavily optimized for speed.
--    For every Lua version the module contains particular implementation branch to get benefits from version-specific features.
--       - branch for Lua 5.1 (emulating bitwise operators using look-up table)
--       - branch for Lua 5.2 (using bit32/bit library), suitable for both Lua 5.2 with native "bit32" and Lua 5.1 with external library "bit"
--       - branch for Lua 5.3/5.4 (using native 64-bit bitwise operators)
--       - branch for Lua 5.3/5.4 (using native 32-bit bitwise operators) for Lua built with LUA_INT_TYPE=LUA_INT_INT
--       - branch for LuaJIT without FFI library (useful in a sandboxed environment)
--       - branch for LuaJIT x86 without FFI library (LuaJIT x86 has oddity because of lack of CPU registers)
--       - branch for LuaJIT 2.0 with FFI library (bit.* functions work only with Lua numbers)
--       - branch for LuaJIT 2.1 with FFI library (bit.* functions can work with "int64_t" arguments)
--
--
-- USAGE:
--    Input data should be provided as a binary string: either as a whole string or as a sequence of substrings (chunk-by-chunk loading, total length < 9*10^15 bytes).
--    Result (SHA digest) is returned in hexadecimal representation as a string of lowercase hex digits.
--    Simplest usage example:
--       local sha = require("sha2")
--       local your_hash = sha.sha256("your string")
--    See file "sha2_test.lua" for more examples.
--
--
-- CHANGELOG:
--  version     date      description
--  -------  ----------   -----------
--     9     2020-05-10   Now works in OpenWrt's Lua (dialect of Lua 5.1 with "double" + "invisible int32")
--     8     2019-09-03   SHA3 functions added
--     7     2019-03-17   Added functions to convert to/from base64
--     6     2018-11-12   HMAC added
--     5     2018-11-10   SHA-1 added
--     4     2018-11-03   MD5 added
--     3     2018-11-02   Bug fixed: incorrect hashing of long (2 GByte) data streams on Lua 5.3/5.4 built with "int32" integers
--     2     2018-10-07   Decreased module loading time in Lua 5.1 implementation branch (thanks to Peter Melnichenko for giving a hint)
--     1     2018-10-06   First release (only SHA-2 functions)
-----------------------------------------------------------------------------

local print_debug_messages = false  -- set to true to view some messages about your system's abilities and implementation branch chosen for your system

local unpack, table_concat, byte, char, string_rep, sub, gsub, gmatch, string_format, floor, ceil, math_min, math_max, tonumber, type =
   table.unpack or unpack, table.concat, string.byte, string.char, string.rep, string.sub, string.gsub, string.gmatch, string.format, math.floor, math.ceil, math.min, math.max, tonumber, type


--------------------------------------------------------------------------------
-- EXAMINING YOUR SYSTEM
--------------------------------------------------------------------------------

bit.lshift = bit.blshift
bit.rshift = bit.blogic_rshift
bit.lrotate = bit32.lrotate
bit.rrotate = bit32.rrotate
function bit.tobit(n) return bit32.band(n, 0xFFFFFFFF) end

local function get_precision(one)
   -- "one" must be either float 1.0 or integer 1
   -- returns bits_precision, is_integer
   -- This function works correctly with all floating point datatypes (including non-IEEE-754)
   local k, n, m, prev_n = 0, one, one
   while true do
      k, prev_n, n, m = k + 1, n, n + n + 1, m + m + k % 2
      if k > 256 or n - (n - 1) ~= 1 or m - (m - 1) ~= 1 or n == m then
         return k, false   -- floating point datatype
      elseif n == prev_n then
         return k, true    -- integer datatype
      end
   end
end

-- Make sure Lua has "double" numbers
local x = 2/3
local Lua_has_double = x * 5 > 3 and x * 4 < 3 and get_precision(1.0) >= 53
assert(Lua_has_double, "at least 53-bit floating point numbers are required")

-- Q:
--    SHA2 was designed for FPU-less machines.
--    So, why floating point numbers are needed for this module?
-- A:
--    53-bit "double" numbers are useful to calculate "magic numbers" used in SHA.
--    I prefer to write 50 LOC "magic numbers calculator" instead of storing more than 200 constants explicitly in this source file.

local int_prec, Lua_has_integers = get_precision(1)
local Lua_has_int64 = Lua_has_integers and int_prec == 64
local Lua_has_int32 = Lua_has_integers and int_prec == 32
assert(Lua_has_int64 or Lua_has_int32 or not Lua_has_integers, "Lua integers must be either 32-bit or 64-bit")

-- Q:
--    Does it mean that almost all non-standard configurations are not supported?
-- A:
--    Yes.  Sorry, too many problems to support all possible Lua numbers configurations.
--       Lua 5.1/5.2    with "int32"               will not work.
--       Lua 5.1/5.2    with "int64"               will not work.
--       Lua 5.1/5.2    with "int128"              will not work.
--       Lua 5.1/5.2    with "float"               will not work.
--       Lua 5.1/5.2    with "double"              is OK.          (default config for Lua 5.1, Lua 5.2, LuaJIT)
--       Lua 5.3/5.4    with "int32"  + "float"    will not work.
--       Lua 5.3/5.4    with "int64"  + "float"    will not work.
--       Lua 5.3/5.4    with "int128" + "float"    will not work.
--       Lua 5.3/5.4    with "int32"  + "double"   is OK.          (config used by Fengari)
--       Lua 5.3/5.4    with "int64"  + "double"   is OK.          (default config for Lua 5.3, Lua 5.4)
--       Lua 5.3/5.4    with "int128" + "double"   will not work.
--   Using floating point numbers better than "double" instead of "double" is OK (non-IEEE-754 floating point implementation are allowed).
--   Using "int128" instead of "int64" is not OK: "int128" would require different branch of implementation for optimized SHA512.

-- Check for LuaJIT and 32-bit bitwise libraries
local is_LuaJIT = ({false, [1] = true})[1] and (type(jit) ~= "table" or jit.version_num >= 20000)  -- LuaJIT 1.x.x is treated as vanilla Lua 5.1
local is_LuaJIT_21  -- LuaJIT 2.1+
local LuaJIT_arch
local ffi           -- LuaJIT FFI library (as a table)
local b             -- 32-bit bitwise library (as a table)
local library_name

if is_LuaJIT then
   -- Assuming "bit" library is always available on LuaJIT
   b = require"bit"
   library_name = "bit"
   -- "ffi" is intentionally disabled on some systems for safety reason
   local LuaJIT_has_FFI, result = pcall(require, "ffi")
   if LuaJIT_has_FFI then
      ffi = result
   end
   is_LuaJIT_21 = not not loadstring"b=0b0"
   LuaJIT_arch = type(jit) == "table" and jit.arch or ffi and ffi.arch or nil
else
   -- For vanilla Lua, "bit"/"bit32" libraries are searched in global namespace only.  No attempt is made to load a library if it's not loaded yet.
   for _, libname in ipairs((_VERSION == "Lua 5.2" or type(_HOST) == "string") and {"bit32", "bit"} or {"bit", "bit32"}) do
      if type(_G[libname]) == "table" and _G[libname].bxor then
         b = _G[libname]
         library_name = libname
         break
      end
   end
end

--------------------------------------------------------------------------------
-- You can disable here some of your system's abilities (for testing purposes)
--------------------------------------------------------------------------------
-- is_LuaJIT = nil
-- is_LuaJIT_21 = nil
-- ffi = nil
-- Lua_has_int32 = nil
-- Lua_has_int64 = nil
-- b, library_name = nil
--------------------------------------------------------------------------------

if print_debug_messages then
   -- Printing list of abilities of your system
   print("Abilities:")
   print("   Lua version:               "..(is_LuaJIT and "LuaJIT "..(is_LuaJIT_21 and "2.1 " or "2.0 ")..(LuaJIT_arch or "")..(ffi and " with FFI" or " without FFI") or _VERSION))
   print("   Integer bitwise operators: "..(Lua_has_int64 and "int64" or Lua_has_int32 and "int32" or "no"))
   print("   32-bit bitwise library:    "..(library_name or "not found"))
end

-- Selecting the most suitable implementation for given set of abilities
local method, branch
if is_LuaJIT and ffi then
   method = "Using 'ffi' library of LuaJIT"
   branch = "FFI"
elseif is_LuaJIT then
   method = "Using special code for FFI-less LuaJIT"
   branch = "LJ"
elseif Lua_has_int64 then
   method = "Using native int64 bitwise operators"
   branch = "INT64"
elseif Lua_has_int32 then
   method = "Using native int32 bitwise operators"
   branch = "INT32"
elseif library_name then   -- when bitwise library is available (Lua 5.2 with native library "bit32" or Lua 5.1 with external library "bit")
   method = "Using '"..library_name.."' library"
   branch = "LIB32"
else
   method = "Emulating bitwise operators using look-up table"
   branch = "EMUL"
end

if print_debug_messages then
   -- Printing the implementation selected to be used on your system
   print("Implementation selected:")
   print("   "..method)
end


--------------------------------------------------------------------------------
-- BASIC 32-BIT BITWISE FUNCTIONS
--------------------------------------------------------------------------------

local AND, OR, XOR, SHL, SHR, ROL, ROR, NOT, NORM, HEX, XOR_BYTE
-- Only low 32 bits of function arguments matter, high bits are ignored
-- The result of all functions (except HEX) is an integer inside "correct range":
--    for "bit" library:    (-2^31)..(2^31-1)
--    for "bit32" library:        0..(2^32-1)

if branch == "FFI" or branch == "LJ" or branch == "LIB32" then

   -- Your system has 32-bit bitwise library (either "bit" or "bit32")

   AND  = b.band                -- 2 arguments
   OR   = b.bor                 -- 2 arguments
   XOR  = b.bxor                -- 2..5 arguments
   SHL  = b.lshift              -- second argument is integer 0..31
   SHR  = b.rshift              -- second argument is integer 0..31
   ROL  = b.rol or b.lrotate    -- second argument is integer 0..31
   ROR  = b.ror or b.rrotate    -- second argument is integer 0..31
   NOT  = b.bnot                -- only for LuaJIT
   NORM = b.tobit               -- only for LuaJIT
   HEX  = b.tohex               -- returns string of 8 lowercase hexadecimal digits
   assert(AND and OR and XOR and SHL and SHR and ROL and ROR and NOT, "Library '"..library_name.."' is incomplete")
   XOR_BYTE = XOR               -- XOR of two bytes (0..255)

elseif branch == "EMUL" then

   -- Emulating 32-bit bitwise operations using 53-bit floating point arithmetic

   function SHL(x, n)
      return (x * 2^n) % 2^32
   end

   function SHR(x, n)
      -- return (x % 2^32 - x % 2^n) / 2^n
      x = x % 2^32 / 2^n
      return x - x % 1
   end

   function ROL(x, n)
      x = x % 2^32 * 2^n
      local r = x % 2^32
      return r + (x - r) / 2^32
   end

   function ROR(x, n)
      x = x % 2^32 / 2^n
      local r = x % 1
      return r * 2^32 + (x - r)
   end

   local AND_of_two_bytes = {[0] = 0}  -- look-up table (256*256 entries)
   local idx = 0
   for y = 0, 127 * 256, 256 do
      for x = y, y + 127 do
         x = AND_of_two_bytes[x] * 2
         AND_of_two_bytes[idx] = x
         AND_of_two_bytes[idx + 1] = x
         AND_of_two_bytes[idx + 256] = x
         AND_of_two_bytes[idx + 257] = x + 1
         idx = idx + 2
      end
      idx = idx + 256
   end

   local function and_or_xor(x, y, operation)
      -- operation: nil = AND, 1 = OR, 2 = XOR
      local x0 = x % 2^32
      local y0 = y % 2^32
      local rx = x0 % 256
      local ry = y0 % 256
      local res = AND_of_two_bytes[rx + ry * 256]
      x = x0 - rx
      y = (y0 - ry) / 256
      rx = x % 65536
      ry = y % 256
      res = res + AND_of_two_bytes[rx + ry] * 256
      x = (x - rx) / 256
      y = (y - ry) / 256
      rx = x % 65536 + y % 256
      res = res + AND_of_two_bytes[rx] * 65536
      res = res + AND_of_two_bytes[(x + y - rx) / 256] * 16777216
      if operation then
         res = x0 + y0 - operation * res
      end
      return res
   end

   function AND(x, y)
      return and_or_xor(x, y)
   end

   function OR(x, y)
      return and_or_xor(x, y, 1)
   end

   function XOR(x, y, z, t, u)          -- 2..5 arguments
      if z then
         if t then
            if u then
               t = and_or_xor(t, u, 2)
            end
            z = and_or_xor(z, t, 2)
         end
         y = and_or_xor(y, z, 2)
      end
      return and_or_xor(x, y, 2)
   end

   function XOR_BYTE(x, y)
      return x + y - 2 * AND_of_two_bytes[x + y * 256]
   end

end

HEX = HEX
   or
      pcall(string_format, "%x", 2^31) and
      function (x)  -- returns string of 8 lowercase hexadecimal digits
         return string_format("%08x", x % 4294967296)
      end
   or
      function (x)  -- for OpenWrt's dialect of Lua
         return string_format("%08x", (x + 2^31) % 2^32 - 2^31)
      end

local function XOR32A5(x)
   return XOR(x, 0xA5A5A5A5) % 4294967296
end

local function create_array_of_lanes()
   return {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
end


--------------------------------------------------------------------------------
-- CREATING OPTIMIZED INNER LOOP
--------------------------------------------------------------------------------

-- Inner loop functions
local sha256_feed_64, sha512_feed_128, md5_feed_64, sha1_feed_64, keccak_feed

-- Arrays of SHA2 "magic numbers" (in "INT64" and "FFI" branches "*_lo" arrays contain 64-bit values)
local sha2_K_lo, sha2_K_hi, sha2_H_lo, sha2_H_hi, sha3_RC_lo, sha3_RC_hi = {}, {}, {}, {}, {}, {}
local sha2_H_ext256 = {[224] = {}, [256] = sha2_H_hi}
local sha2_H_ext512_lo, sha2_H_ext512_hi = {[384] = {}, [512] = sha2_H_lo}, {[384] = {}, [512] = sha2_H_hi}
local md5_K, md5_sha1_H = {}, {0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0}
local md5_next_shift = {0, 0, 0, 0, 0, 0, 0, 0, 28, 25, 26, 27, 0, 0, 10, 9, 11, 12, 0, 15, 16, 17, 18, 0, 20, 22, 23, 21}
local HEX64, XOR64A5, lanes_index_base  -- defined only for branches that internally use 64-bit integers: "INT64" and "FFI"
local common_W = {}    -- temporary table shared between all calculations (to avoid creating new temporary table every time)
local K_lo_modulo, hi_factor, hi_factor_keccak = 4294967296, 0, 0

local function build_keccak_format(elem)
   local keccak_format = {}
   for _, size in ipairs{1, 9, 13, 17, 18, 21} do
      keccak_format[size] = "<"..string_rep(elem, size)
   end
   return keccak_format
end


if branch == "FFI" then


   -- SHA256 implementation for "LuaJIT with FFI" branch

   local common_W_FFI_int32 = ffi.new"int32_t[80]"   -- 64 is enough for SHA256, but 80 is needed for SHA-1

   function sha256_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K = common_W_FFI_int32, sha2_K_hi
      for pos = offs, offs + size - 1, 64 do
         for j = 0, 15 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)   -- slow, but doesn't depend on endianness
            W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
         end
         for j = 16, 63 do
            local a, b = W[j-15], W[j-2]
            W[j] = NORM( XOR(ROR(a, 7), ROL(a, 14), SHR(a, 3)) + XOR(ROL(b, 15), ROL(b, 13), SHR(b, 10)) + W[j-7] + W[j-16] )
         end
         local a, b, c, d, e, f, g, h = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
         for j = 0, 63, 8 do  -- Thanks to Peter Cawley for this workaround (unroll the loop to avoid "PHI shuffling too complex" due to PHIs overlap)
            local z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j] + K[j+1] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+1] + K[j+2] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+2] + K[j+3] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+3] + K[j+4] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+4] + K[j+5] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+5] + K[j+6] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+6] + K[j+7] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(g, AND(e, XOR(f, g))) + XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + (W[j+7] + K[j+8] + h) )
            h, g, f, e = g, f, e, NORM( d + z )
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
         end
         H[1], H[2], H[3], H[4] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4])
         H[5], H[6], H[7], H[8] = NORM(e + H[5]), NORM(f + H[6]), NORM(g + H[7]), NORM(h + H[8])
      end
   end

   local common_W_FFI_int64 = ffi.new"int64_t[80]"
   local int64 = ffi.typeof"int64_t"
   local int32 = ffi.typeof"int32_t"
   local uint32 = ffi.typeof"uint32_t"

   hi_factor = int64(2^32)

   if is_LuaJIT_21 then   -- LuaJIT 2.1 supports bitwise 64-bit operations

      local AND64, OR64, XOR64, NOT64, SHL64, SHR64, ROL64, ROR64  -- introducing synonyms for better code readability
          = AND,   OR,   XOR,   NOT,   SHL,   SHR,   ROL,   ROR
      HEX64 = HEX


      -- SHA3 implementation for "LuaJIT 2.1 + FFI" branch

      local lanes_arr64 = ffi.typeof"int64_t[30]"  -- 25 + 5 for temporary usage
      -- lanes array is indexed from 0
      lanes_index_base = 0
      hi_factor_keccak = int64(2^32)

      function create_array_of_lanes()
         return lanes_arr64()
      end

      function keccak_feed(lanes, _, str, offs, size, block_size_in_bytes)
         -- offs >= 0, size >= 0, size is multiple of block_size_in_bytes, block_size_in_bytes is positive multiple of 8
         local RC = sha3_RC_lo
         local qwords_qty = SHR(block_size_in_bytes, 3)
         for pos = offs, offs + size - 1, block_size_in_bytes do
            for j = 0, qwords_qty - 1 do
               pos = pos + 8
               local h, g, f, e, d, c, b, a = byte(str, pos - 7, pos)   -- slow, but doesn't depend on endianness
               lanes[j] = XOR64(lanes[j], OR64(OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d) * int64(2^32), uint32(int32(OR(SHL(e, 24), SHL(f, 16), SHL(g, 8), h)))))
            end
            for round_idx = 1, 24 do
               for j = 0, 4 do
                  lanes[25 + j] = XOR64(lanes[j], lanes[j+5], lanes[j+10], lanes[j+15], lanes[j+20])
               end
               local D = XOR64(lanes[25], ROL64(lanes[27], 1))
               lanes[1], lanes[6], lanes[11], lanes[16] = ROL64(XOR64(D, lanes[6]), 44), ROL64(XOR64(D, lanes[16]), 45), ROL64(XOR64(D, lanes[1]), 1), ROL64(XOR64(D, lanes[11]), 10)
               lanes[21] = ROL64(XOR64(D, lanes[21]), 2)
               D = XOR64(lanes[26], ROL64(lanes[28], 1))
               lanes[2], lanes[7], lanes[12], lanes[22] = ROL64(XOR64(D, lanes[12]), 43), ROL64(XOR64(D, lanes[22]), 61), ROL64(XOR64(D, lanes[7]), 6), ROL64(XOR64(D, lanes[2]), 62)
               lanes[17] = ROL64(XOR64(D, lanes[17]), 15)
               D = XOR64(lanes[27], ROL64(lanes[29], 1))
               lanes[3], lanes[8], lanes[18], lanes[23] = ROL64(XOR64(D, lanes[18]), 21), ROL64(XOR64(D, lanes[3]), 28), ROL64(XOR64(D, lanes[23]), 56), ROL64(XOR64(D, lanes[8]), 55)
               lanes[13] = ROL64(XOR64(D, lanes[13]), 25)
               D = XOR64(lanes[28], ROL64(lanes[25], 1))
               lanes[4], lanes[14], lanes[19], lanes[24] = ROL64(XOR64(D, lanes[24]), 14), ROL64(XOR64(D, lanes[19]), 8), ROL64(XOR64(D, lanes[4]), 27), ROL64(XOR64(D, lanes[14]), 39)
               lanes[9] = ROL64(XOR64(D, lanes[9]), 20)
               D = XOR64(lanes[29], ROL64(lanes[26], 1))
               lanes[5], lanes[10], lanes[15], lanes[20] = ROL64(XOR64(D, lanes[10]), 3), ROL64(XOR64(D, lanes[20]), 18), ROL64(XOR64(D, lanes[5]), 36), ROL64(XOR64(D, lanes[15]), 41)
               lanes[0] = XOR64(D, lanes[0])
               lanes[0], lanes[1], lanes[2], lanes[3], lanes[4] = XOR64(lanes[0], AND64(NOT64(lanes[1]), lanes[2]), RC[round_idx]), XOR64(lanes[1], AND64(NOT64(lanes[2]), lanes[3])), XOR64(lanes[2], AND64(NOT64(lanes[3]), lanes[4])), XOR64(lanes[3], AND64(NOT64(lanes[4]), lanes[0])), XOR64(lanes[4], AND64(NOT64(lanes[0]), lanes[1]))
               lanes[5], lanes[6], lanes[7], lanes[8], lanes[9] = XOR64(lanes[8], AND64(NOT64(lanes[9]), lanes[5])), XOR64(lanes[9], AND64(NOT64(lanes[5]), lanes[6])), XOR64(lanes[5], AND64(NOT64(lanes[6]), lanes[7])), XOR64(lanes[6], AND64(NOT64(lanes[7]), lanes[8])), XOR64(lanes[7], AND64(NOT64(lanes[8]), lanes[9]))
               lanes[10], lanes[11], lanes[12], lanes[13], lanes[14] = XOR64(lanes[11], AND64(NOT64(lanes[12]), lanes[13])), XOR64(lanes[12], AND64(NOT64(lanes[13]), lanes[14])), XOR64(lanes[13], AND64(NOT64(lanes[14]), lanes[10])), XOR64(lanes[14], AND64(NOT64(lanes[10]), lanes[11])), XOR64(lanes[10], AND64(NOT64(lanes[11]), lanes[12]))
               lanes[15], lanes[16], lanes[17], lanes[18], lanes[19] = XOR64(lanes[19], AND64(NOT64(lanes[15]), lanes[16])), XOR64(lanes[15], AND64(NOT64(lanes[16]), lanes[17])), XOR64(lanes[16], AND64(NOT64(lanes[17]), lanes[18])), XOR64(lanes[17], AND64(NOT64(lanes[18]), lanes[19])), XOR64(lanes[18], AND64(NOT64(lanes[19]), lanes[15]))
               lanes[20], lanes[21], lanes[22], lanes[23], lanes[24] = XOR64(lanes[22], AND64(NOT64(lanes[23]), lanes[24])), XOR64(lanes[23], AND64(NOT64(lanes[24]), lanes[20])), XOR64(lanes[24], AND64(NOT64(lanes[20]), lanes[21])), XOR64(lanes[20], AND64(NOT64(lanes[21]), lanes[22])), XOR64(lanes[21], AND64(NOT64(lanes[22]), lanes[23]))
            end
         end
      end


      -- SHA512 implementation for "LuaJIT 2.1 + FFI" branch

      local A5_long = 0xA5A5A5A5 * int64(2^32 + 1)  -- It's impossible to use constant 0xA5A5A5A5A5A5A5A5LL because it will raise syntax error on other Lua versions

      function XOR64A5(long)
         return XOR64(long, A5_long)
      end

      function sha512_feed_128(H, _, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 128
         local W, K = common_W_FFI_int64, sha2_K_lo
         for pos = offs, offs + size - 1, 128 do
            for j = 0, 15 do
               pos = pos + 8
               local a, b, c, d, e, f, g, h = byte(str, pos - 7, pos)   -- slow, but doesn't depend on endianness
               W[j] = OR64(OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d) * int64(2^32), uint32(int32(OR(SHL(e, 24), SHL(f, 16), SHL(g, 8), h))))
            end
            for j = 16, 79 do
               local a, b = W[j-15], W[j-2]
               W[j] = XOR64(ROR64(a, 1), ROR64(a, 8), SHR64(a, 7)) + XOR64(ROR64(b, 19), ROL64(b, 3), SHR64(b, 6)) + W[j-7] + W[j-16]
            end
            local a, b, c, d, e, f, g, h = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
            for j = 0, 79, 8 do
               local z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+1] + W[j]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+2] + W[j+1]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+3] + W[j+2]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+4] + W[j+3]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+5] + W[j+4]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+6] + W[j+5]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+7] + W[j+6]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
               z = XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23)) + XOR64(g, AND64(e, XOR64(f, g))) + h + K[j+8] + W[j+7]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XOR64(AND64(XOR64(a, b), c), AND64(a, b)) + XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30)) + z
            end
            H[1] = a + H[1]
            H[2] = b + H[2]
            H[3] = c + H[3]
            H[4] = d + H[4]
            H[5] = e + H[5]
            H[6] = f + H[6]
            H[7] = g + H[7]
            H[8] = h + H[8]
         end
      end

   else  -- LuaJIT 2.0 doesn't support 64-bit bitwise operations


      -- SHA512 implementation for "LuaJIT 2.0 + FFI" branch

      local union64 = ffi.typeof"union{int64_t i64; struct{int32_t lo, hi;} i32;}"
      do  -- make sure the struct is endianness-compatible
         local u = union64(1)
         if u.i32.lo < u.i32.hi then
            union64 = ffi.typeof"union{int64_t i64; struct{int32_t hi, lo;} i32;}"
         end
      end
      local unions64 = ffi.typeof("$[?]", union64)
      local U = unions64(3)   -- this array of unions is used for fast splitting int64 into int32_high and int32_low

      -- "xorrific" 64-bit functions :-)
      -- int64 input is splitted into two int32 parts, some bitwise 32-bit operations are performed, finally the result is converted to int64
      -- these functions are needed because bit.* functions in LuaJIT 2.0 don't work with int64_t

      local function XORROR64_1(a)
         -- return XOR64(ROR64(a, 1), ROR64(a, 8), SHR64(a, 7))
         U[0].i64 = a
         local a_lo, a_hi = U[0].i32.lo, U[0].i32.hi
         local t_lo = XOR(OR(SHR(a_lo, 1), SHL(a_hi, 31)), OR(SHR(a_lo, 8), SHL(a_hi, 24)), OR(SHR(a_lo, 7), SHL(a_hi, 25)))
         local t_hi = XOR(OR(SHR(a_hi, 1), SHL(a_lo, 31)), OR(SHR(a_hi, 8), SHL(a_lo, 24)), SHR(a_hi, 7))
         return t_hi * int64(2^32) + uint32(int32(t_lo))
      end

      local function XORROR64_2(b)
         -- return XOR64(ROR64(b, 19), ROL64(b, 3), SHR64(b, 6))
         U[0].i64 = b
         local b_lo, b_hi = U[0].i32.lo, U[0].i32.hi
         local u_lo = XOR(OR(SHR(b_lo, 19), SHL(b_hi, 13)), OR(SHL(b_lo, 3), SHR(b_hi, 29)), OR(SHR(b_lo, 6), SHL(b_hi, 26)))
         local u_hi = XOR(OR(SHR(b_hi, 19), SHL(b_lo, 13)), OR(SHL(b_hi, 3), SHR(b_lo, 29)), SHR(b_hi, 6))
         return u_hi * int64(2^32) + uint32(int32(u_lo))
      end

      local function XORROR64_3(e)
         -- return XOR64(ROR64(e, 14), ROR64(e, 18), ROL64(e, 23))
         U[0].i64 = e
         local e_lo, e_hi = U[0].i32.lo, U[0].i32.hi
         local u_lo = XOR(OR(SHR(e_lo, 14), SHL(e_hi, 18)), OR(SHR(e_lo, 18), SHL(e_hi, 14)), OR(SHL(e_lo, 23), SHR(e_hi, 9)))
         local u_hi = XOR(OR(SHR(e_hi, 14), SHL(e_lo, 18)), OR(SHR(e_hi, 18), SHL(e_lo, 14)), OR(SHL(e_hi, 23), SHR(e_lo, 9)))
         return u_hi * int64(2^32) + uint32(int32(u_lo))
      end

      local function XORROR64_6(a)
         -- return XOR64(ROR64(a, 28), ROL64(a, 25), ROL64(a, 30))
         U[0].i64 = a
         local b_lo, b_hi = U[0].i32.lo, U[0].i32.hi
         local u_lo = XOR(OR(SHR(b_lo, 28), SHL(b_hi, 4)), OR(SHL(b_lo, 30), SHR(b_hi, 2)), OR(SHL(b_lo, 25), SHR(b_hi, 7)))
         local u_hi = XOR(OR(SHR(b_hi, 28), SHL(b_lo, 4)), OR(SHL(b_hi, 30), SHR(b_lo, 2)), OR(SHL(b_hi, 25), SHR(b_lo, 7)))
         return u_hi * int64(2^32) + uint32(int32(u_lo))
      end

      local function XORROR64_4(e, f, g)
         -- return XOR64(g, AND64(e, XOR64(f, g)))
         U[0].i64 = f
         U[1].i64 = g
         U[2].i64 = e
         local f_lo, f_hi = U[0].i32.lo, U[0].i32.hi
         local g_lo, g_hi = U[1].i32.lo, U[1].i32.hi
         local e_lo, e_hi = U[2].i32.lo, U[2].i32.hi
         local result_lo = XOR(g_lo, AND(e_lo, XOR(f_lo, g_lo)))
         local result_hi = XOR(g_hi, AND(e_hi, XOR(f_hi, g_hi)))
         return result_hi * int64(2^32) + uint32(int32(result_lo))
      end

      local function XORROR64_5(a, b, c)
         -- return XOR64(AND64(XOR64(a, b), c), AND64(a, b))
         U[0].i64 = a
         U[1].i64 = b
         U[2].i64 = c
         local a_lo, a_hi = U[0].i32.lo, U[0].i32.hi
         local b_lo, b_hi = U[1].i32.lo, U[1].i32.hi
         local c_lo, c_hi = U[2].i32.lo, U[2].i32.hi
         local result_lo = XOR(AND(XOR(a_lo, b_lo), c_lo), AND(a_lo, b_lo))
         local result_hi = XOR(AND(XOR(a_hi, b_hi), c_hi), AND(a_hi, b_hi))
         return result_hi * int64(2^32) + uint32(int32(result_lo))
      end

      function XOR64A5(long)
         -- return XOR64(long, 0xA5A5A5A5A5A5A5A5)
         U[0].i64 = long
         local lo32, hi32 = U[0].i32.lo, U[0].i32.hi
         lo32 = XOR(lo32, 0xA5A5A5A5)
         hi32 = XOR(hi32, 0xA5A5A5A5)
         return hi32 * int64(2^32) + uint32(int32(lo32))
      end

      function HEX64(long)
         U[0].i64 = long
         return HEX(U[0].i32.hi)..HEX(U[0].i32.lo)
      end

      function sha512_feed_128(H, _, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 128
         local W, K = common_W_FFI_int64, sha2_K_lo
         for pos = offs, offs + size - 1, 128 do
            for j = 0, 15 do
               pos = pos + 8
               local a, b, c, d, e, f, g, h = byte(str, pos - 7, pos)   -- slow, but doesn't depend on endianness
               W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d) * int64(2^32) + uint32(int32(OR(SHL(e, 24), SHL(f, 16), SHL(g, 8), h)))
            end
            for j = 16, 79 do
               W[j] = XORROR64_1(W[j-15]) + XORROR64_2(W[j-2]) + W[j-7] + W[j-16]
            end
            local a, b, c, d, e, f, g, h = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
            for j = 0, 79, 8 do
               local z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+1] + W[j]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+2] + W[j+1]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+3] + W[j+2]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+4] + W[j+3]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+5] + W[j+4]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+6] + W[j+5]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+7] + W[j+6]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
               z = XORROR64_3(e) + XORROR64_4(e, f, g) + h + K[j+8] + W[j+7]
               h, g, f, e = g, f, e, z + d
               d, c, b, a = c, b, a, XORROR64_5(a, b, c) + XORROR64_6(a) + z
            end
            H[1] = a + H[1]
            H[2] = b + H[2]
            H[3] = c + H[3]
            H[4] = d + H[4]
            H[5] = e + H[5]
            H[6] = f + H[6]
            H[7] = g + H[7]
            H[8] = h + H[8]
         end
      end

   end


   -- MD5 implementation for "LuaJIT with FFI" branch

   function md5_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K = common_W_FFI_int32, md5_K
      for pos = offs, offs + size - 1, 64 do
         for j = 0, 15 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)   -- slow, but doesn't depend on endianness
            W[j] = OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a)
         end
         local a, b, c, d = H[1], H[2], H[3], H[4]
         for j = 0, 15, 4 do
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+1] + W[j  ] + a),  7) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+2] + W[j+1] + a), 12) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+3] + W[j+2] + a), 17) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+4] + W[j+3] + a), 22) + b)
         end
         for j = 16, 31, 4 do
            local g = 5*j
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+1] + W[AND(g + 1, 15)] + a),  5) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+2] + W[AND(g + 6, 15)] + a),  9) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+3] + W[AND(g - 5, 15)] + a), 14) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+4] + W[AND(g    , 15)] + a), 20) + b)
         end
         for j = 32, 47, 4 do
            local g = 3*j
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+1] + W[AND(g + 5, 15)] + a),  4) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+2] + W[AND(g + 8, 15)] + a), 11) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+3] + W[AND(g - 5, 15)] + a), 16) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+4] + W[AND(g - 2, 15)] + a), 23) + b)
         end
         for j = 48, 63, 4 do
            local g = 7*j
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+1] + W[AND(g    , 15)] + a),  6) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+2] + W[AND(g + 7, 15)] + a), 10) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+3] + W[AND(g - 2, 15)] + a), 15) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+4] + W[AND(g + 5, 15)] + a), 21) + b)
         end
         H[1], H[2], H[3], H[4] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4])
      end
   end


   -- SHA-1 implementation for "LuaJIT with FFI" branch

   function sha1_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W = common_W_FFI_int32
      for pos = offs, offs + size - 1, 64 do
         for j = 0, 15 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)   -- slow, but doesn't depend on endianness
            W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
         end
         for j = 16, 79 do
            W[j] = ROL(XOR(W[j-3], W[j-8], W[j-14], W[j-16]), 1)
         end
         local a, b, c, d, e = H[1], H[2], H[3], H[4], H[5]
         for j = 0, 19, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j]   + 0x5A827999 + e))          -- constant = floor(2^30 * sqrt(2))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+1] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+2] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+3] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+4] + 0x5A827999 + e))
         end
         for j = 20, 39, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j]   + 0x6ED9EBA1 + e))                       -- 2^30 * sqrt(3)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+1] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+2] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+3] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+4] + 0x6ED9EBA1 + e))
         end
         for j = 40, 59, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j]   + 0x8F1BBCDC + e))  -- 2^30 * sqrt(5)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+1] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+2] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+3] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+4] + 0x8F1BBCDC + e))
         end
         for j = 60, 79, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j]   + 0xCA62C1D6 + e))                       -- 2^30 * sqrt(10)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+1] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+2] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+3] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+4] + 0xCA62C1D6 + e))
         end
         H[1], H[2], H[3], H[4], H[5] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4]), NORM(e + H[5])
      end
   end

end


-- SHA3 implementation for "LuaJIT 2.0 + FFI" and "LuaJIT without FFI" branches

if branch == "FFI" and not is_LuaJIT_21 or branch == "LJ" then

   if branch == "FFI" then
      local lanes_arr32 = ffi.typeof"int32_t[31]"  -- 25 + 5 + 1 (due to 1-based indexing)

      function create_array_of_lanes()
         return lanes_arr32()
      end

   end

   function keccak_feed(lanes_lo, lanes_hi, str, offs, size, block_size_in_bytes)
      -- offs >= 0, size >= 0, size is multiple of block_size_in_bytes, block_size_in_bytes is positive multiple of 8
      local RC_lo, RC_hi = sha3_RC_lo, sha3_RC_hi
      local qwords_qty = SHR(block_size_in_bytes, 3)
      for pos = offs, offs + size - 1, block_size_in_bytes do
         for j = 1, qwords_qty do
            local a, b, c, d = byte(str, pos + 1, pos + 4)
            lanes_lo[j] = XOR(lanes_lo[j], OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a))
            pos = pos + 8
            a, b, c, d = byte(str, pos - 3, pos)
            lanes_hi[j] = XOR(lanes_hi[j], OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a))
         end
         for round_idx = 1, 24 do
            for j = 1, 5 do
               lanes_lo[25 + j] = XOR(lanes_lo[j], lanes_lo[j + 5], lanes_lo[j + 10], lanes_lo[j + 15], lanes_lo[j + 20])
            end
            for j = 1, 5 do
               lanes_hi[25 + j] = XOR(lanes_hi[j], lanes_hi[j + 5], lanes_hi[j + 10], lanes_hi[j + 15], lanes_hi[j + 20])
            end
            local D_lo = XOR(lanes_lo[26], SHL(lanes_lo[28], 1), SHR(lanes_hi[28], 31))
            local D_hi = XOR(lanes_hi[26], SHL(lanes_hi[28], 1), SHR(lanes_lo[28], 31))
            lanes_lo[2], lanes_hi[2], lanes_lo[7], lanes_hi[7], lanes_lo[12], lanes_hi[12], lanes_lo[17], lanes_hi[17] = XOR(SHR(XOR(D_lo, lanes_lo[7]), 20), SHL(XOR(D_hi, lanes_hi[7]), 12)), XOR(SHR(XOR(D_hi, lanes_hi[7]), 20), SHL(XOR(D_lo, lanes_lo[7]), 12)), XOR(SHR(XOR(D_lo, lanes_lo[17]), 19), SHL(XOR(D_hi, lanes_hi[17]), 13)), XOR(SHR(XOR(D_hi, lanes_hi[17]), 19), SHL(XOR(D_lo, lanes_lo[17]), 13)), XOR(SHL(XOR(D_lo, lanes_lo[2]), 1), SHR(XOR(D_hi, lanes_hi[2]), 31)), XOR(SHL(XOR(D_hi, lanes_hi[2]), 1), SHR(XOR(D_lo, lanes_lo[2]), 31)), XOR(SHL(XOR(D_lo, lanes_lo[12]), 10), SHR(XOR(D_hi, lanes_hi[12]), 22)), XOR(SHL(XOR(D_hi, lanes_hi[12]), 10), SHR(XOR(D_lo, lanes_lo[12]), 22))
            local L, H = XOR(D_lo, lanes_lo[22]), XOR(D_hi, lanes_hi[22])
            lanes_lo[22], lanes_hi[22] = XOR(SHL(L, 2), SHR(H, 30)), XOR(SHL(H, 2), SHR(L, 30))
            D_lo = XOR(lanes_lo[27], SHL(lanes_lo[29], 1), SHR(lanes_hi[29], 31))
            D_hi = XOR(lanes_hi[27], SHL(lanes_hi[29], 1), SHR(lanes_lo[29], 31))
            lanes_lo[3], lanes_hi[3], lanes_lo[8], lanes_hi[8], lanes_lo[13], lanes_hi[13], lanes_lo[23], lanes_hi[23] = XOR(SHR(XOR(D_lo, lanes_lo[13]), 21), SHL(XOR(D_hi, lanes_hi[13]), 11)), XOR(SHR(XOR(D_hi, lanes_hi[13]), 21), SHL(XOR(D_lo, lanes_lo[13]), 11)), XOR(SHR(XOR(D_lo, lanes_lo[23]), 3), SHL(XOR(D_hi, lanes_hi[23]), 29)), XOR(SHR(XOR(D_hi, lanes_hi[23]), 3), SHL(XOR(D_lo, lanes_lo[23]), 29)), XOR(SHL(XOR(D_lo, lanes_lo[8]), 6), SHR(XOR(D_hi, lanes_hi[8]), 26)), XOR(SHL(XOR(D_hi, lanes_hi[8]), 6), SHR(XOR(D_lo, lanes_lo[8]), 26)), XOR(SHR(XOR(D_lo, lanes_lo[3]), 2), SHL(XOR(D_hi, lanes_hi[3]), 30)), XOR(SHR(XOR(D_hi, lanes_hi[3]), 2), SHL(XOR(D_lo, lanes_lo[3]), 30))
            L, H = XOR(D_lo, lanes_lo[18]), XOR(D_hi, lanes_hi[18])
            lanes_lo[18], lanes_hi[18] = XOR(SHL(L, 15), SHR(H, 17)), XOR(SHL(H, 15), SHR(L, 17))
            D_lo = XOR(lanes_lo[28], SHL(lanes_lo[30], 1), SHR(lanes_hi[30], 31))
            D_hi = XOR(lanes_hi[28], SHL(lanes_hi[30], 1), SHR(lanes_lo[30], 31))
            lanes_lo[4], lanes_hi[4], lanes_lo[9], lanes_hi[9], lanes_lo[19], lanes_hi[19], lanes_lo[24], lanes_hi[24] = XOR(SHL(XOR(D_lo, lanes_lo[19]), 21), SHR(XOR(D_hi, lanes_hi[19]), 11)), XOR(SHL(XOR(D_hi, lanes_hi[19]), 21), SHR(XOR(D_lo, lanes_lo[19]), 11)), XOR(SHL(XOR(D_lo, lanes_lo[4]), 28), SHR(XOR(D_hi, lanes_hi[4]), 4)), XOR(SHL(XOR(D_hi, lanes_hi[4]), 28), SHR(XOR(D_lo, lanes_lo[4]), 4)), XOR(SHR(XOR(D_lo, lanes_lo[24]), 8), SHL(XOR(D_hi, lanes_hi[24]), 24)), XOR(SHR(XOR(D_hi, lanes_hi[24]), 8), SHL(XOR(D_lo, lanes_lo[24]), 24)), XOR(SHR(XOR(D_lo, lanes_lo[9]), 9), SHL(XOR(D_hi, lanes_hi[9]), 23)), XOR(SHR(XOR(D_hi, lanes_hi[9]), 9), SHL(XOR(D_lo, lanes_lo[9]), 23))
            L, H = XOR(D_lo, lanes_lo[14]), XOR(D_hi, lanes_hi[14])
            lanes_lo[14], lanes_hi[14] = XOR(SHL(L, 25), SHR(H, 7)), XOR(SHL(H, 25), SHR(L, 7))
            D_lo = XOR(lanes_lo[29], SHL(lanes_lo[26], 1), SHR(lanes_hi[26], 31))
            D_hi = XOR(lanes_hi[29], SHL(lanes_hi[26], 1), SHR(lanes_lo[26], 31))
            lanes_lo[5], lanes_hi[5], lanes_lo[15], lanes_hi[15], lanes_lo[20], lanes_hi[20], lanes_lo[25], lanes_hi[25] = XOR(SHL(XOR(D_lo, lanes_lo[25]), 14), SHR(XOR(D_hi, lanes_hi[25]), 18)), XOR(SHL(XOR(D_hi, lanes_hi[25]), 14), SHR(XOR(D_lo, lanes_lo[25]), 18)), XOR(SHL(XOR(D_lo, lanes_lo[20]), 8), SHR(XOR(D_hi, lanes_hi[20]), 24)), XOR(SHL(XOR(D_hi, lanes_hi[20]), 8), SHR(XOR(D_lo, lanes_lo[20]), 24)), XOR(SHL(XOR(D_lo, lanes_lo[5]), 27), SHR(XOR(D_hi, lanes_hi[5]), 5)), XOR(SHL(XOR(D_hi, lanes_hi[5]), 27), SHR(XOR(D_lo, lanes_lo[5]), 5)), XOR(SHR(XOR(D_lo, lanes_lo[15]), 25), SHL(XOR(D_hi, lanes_hi[15]), 7)), XOR(SHR(XOR(D_hi, lanes_hi[15]), 25), SHL(XOR(D_lo, lanes_lo[15]), 7))
            L, H = XOR(D_lo, lanes_lo[10]), XOR(D_hi, lanes_hi[10])
            lanes_lo[10], lanes_hi[10] = XOR(SHL(L, 20), SHR(H, 12)), XOR(SHL(H, 20), SHR(L, 12))
            D_lo = XOR(lanes_lo[30], SHL(lanes_lo[27], 1), SHR(lanes_hi[27], 31))
            D_hi = XOR(lanes_hi[30], SHL(lanes_hi[27], 1), SHR(lanes_lo[27], 31))
            lanes_lo[6], lanes_hi[6], lanes_lo[11], lanes_hi[11], lanes_lo[16], lanes_hi[16], lanes_lo[21], lanes_hi[21] = XOR(SHL(XOR(D_lo, lanes_lo[11]), 3), SHR(XOR(D_hi, lanes_hi[11]), 29)), XOR(SHL(XOR(D_hi, lanes_hi[11]), 3), SHR(XOR(D_lo, lanes_lo[11]), 29)), XOR(SHL(XOR(D_lo, lanes_lo[21]), 18), SHR(XOR(D_hi, lanes_hi[21]), 14)), XOR(SHL(XOR(D_hi, lanes_hi[21]), 18), SHR(XOR(D_lo, lanes_lo[21]), 14)), XOR(SHR(XOR(D_lo, lanes_lo[6]), 28), SHL(XOR(D_hi, lanes_hi[6]), 4)), XOR(SHR(XOR(D_hi, lanes_hi[6]), 28), SHL(XOR(D_lo, lanes_lo[6]), 4)), XOR(SHR(XOR(D_lo, lanes_lo[16]), 23), SHL(XOR(D_hi, lanes_hi[16]), 9)), XOR(SHR(XOR(D_hi, lanes_hi[16]), 23), SHL(XOR(D_lo, lanes_lo[16]), 9))
            lanes_lo[1], lanes_hi[1] = XOR(D_lo, lanes_lo[1]), XOR(D_hi, lanes_hi[1])
            lanes_lo[1], lanes_lo[2], lanes_lo[3], lanes_lo[4], lanes_lo[5] = XOR(lanes_lo[1], AND(NOT(lanes_lo[2]), lanes_lo[3]), RC_lo[round_idx]), XOR(lanes_lo[2], AND(NOT(lanes_lo[3]), lanes_lo[4])), XOR(lanes_lo[3], AND(NOT(lanes_lo[4]), lanes_lo[5])), XOR(lanes_lo[4], AND(NOT(lanes_lo[5]), lanes_lo[1])), XOR(lanes_lo[5], AND(NOT(lanes_lo[1]), lanes_lo[2]))
            lanes_lo[6], lanes_lo[7], lanes_lo[8], lanes_lo[9], lanes_lo[10] = XOR(lanes_lo[9], AND(NOT(lanes_lo[10]), lanes_lo[6])), XOR(lanes_lo[10], AND(NOT(lanes_lo[6]), lanes_lo[7])), XOR(lanes_lo[6], AND(NOT(lanes_lo[7]), lanes_lo[8])), XOR(lanes_lo[7], AND(NOT(lanes_lo[8]), lanes_lo[9])), XOR(lanes_lo[8], AND(NOT(lanes_lo[9]), lanes_lo[10]))
            lanes_lo[11], lanes_lo[12], lanes_lo[13], lanes_lo[14], lanes_lo[15] = XOR(lanes_lo[12], AND(NOT(lanes_lo[13]), lanes_lo[14])), XOR(lanes_lo[13], AND(NOT(lanes_lo[14]), lanes_lo[15])), XOR(lanes_lo[14], AND(NOT(lanes_lo[15]), lanes_lo[11])), XOR(lanes_lo[15], AND(NOT(lanes_lo[11]), lanes_lo[12])), XOR(lanes_lo[11], AND(NOT(lanes_lo[12]), lanes_lo[13]))
            lanes_lo[16], lanes_lo[17], lanes_lo[18], lanes_lo[19], lanes_lo[20] = XOR(lanes_lo[20], AND(NOT(lanes_lo[16]), lanes_lo[17])), XOR(lanes_lo[16], AND(NOT(lanes_lo[17]), lanes_lo[18])), XOR(lanes_lo[17], AND(NOT(lanes_lo[18]), lanes_lo[19])), XOR(lanes_lo[18], AND(NOT(lanes_lo[19]), lanes_lo[20])), XOR(lanes_lo[19], AND(NOT(lanes_lo[20]), lanes_lo[16]))
            lanes_lo[21], lanes_lo[22], lanes_lo[23], lanes_lo[24], lanes_lo[25] = XOR(lanes_lo[23], AND(NOT(lanes_lo[24]), lanes_lo[25])), XOR(lanes_lo[24], AND(NOT(lanes_lo[25]), lanes_lo[21])), XOR(lanes_lo[25], AND(NOT(lanes_lo[21]), lanes_lo[22])), XOR(lanes_lo[21], AND(NOT(lanes_lo[22]), lanes_lo[23])), XOR(lanes_lo[22], AND(NOT(lanes_lo[23]), lanes_lo[24]))
            lanes_hi[1], lanes_hi[2], lanes_hi[3], lanes_hi[4], lanes_hi[5] = XOR(lanes_hi[1], AND(NOT(lanes_hi[2]), lanes_hi[3]), RC_hi[round_idx]), XOR(lanes_hi[2], AND(NOT(lanes_hi[3]), lanes_hi[4])), XOR(lanes_hi[3], AND(NOT(lanes_hi[4]), lanes_hi[5])), XOR(lanes_hi[4], AND(NOT(lanes_hi[5]), lanes_hi[1])), XOR(lanes_hi[5], AND(NOT(lanes_hi[1]), lanes_hi[2]))
            lanes_hi[6], lanes_hi[7], lanes_hi[8], lanes_hi[9], lanes_hi[10] = XOR(lanes_hi[9], AND(NOT(lanes_hi[10]), lanes_hi[6])), XOR(lanes_hi[10], AND(NOT(lanes_hi[6]), lanes_hi[7])), XOR(lanes_hi[6], AND(NOT(lanes_hi[7]), lanes_hi[8])), XOR(lanes_hi[7], AND(NOT(lanes_hi[8]), lanes_hi[9])), XOR(lanes_hi[8], AND(NOT(lanes_hi[9]), lanes_hi[10]))
            lanes_hi[11], lanes_hi[12], lanes_hi[13], lanes_hi[14], lanes_hi[15] = XOR(lanes_hi[12], AND(NOT(lanes_hi[13]), lanes_hi[14])), XOR(lanes_hi[13], AND(NOT(lanes_hi[14]), lanes_hi[15])), XOR(lanes_hi[14], AND(NOT(lanes_hi[15]), lanes_hi[11])), XOR(lanes_hi[15], AND(NOT(lanes_hi[11]), lanes_hi[12])), XOR(lanes_hi[11], AND(NOT(lanes_hi[12]), lanes_hi[13]))
            lanes_hi[16], lanes_hi[17], lanes_hi[18], lanes_hi[19], lanes_hi[20] = XOR(lanes_hi[20], AND(NOT(lanes_hi[16]), lanes_hi[17])), XOR(lanes_hi[16], AND(NOT(lanes_hi[17]), lanes_hi[18])), XOR(lanes_hi[17], AND(NOT(lanes_hi[18]), lanes_hi[19])), XOR(lanes_hi[18], AND(NOT(lanes_hi[19]), lanes_hi[20])), XOR(lanes_hi[19], AND(NOT(lanes_hi[20]), lanes_hi[16]))
            lanes_hi[21], lanes_hi[22], lanes_hi[23], lanes_hi[24], lanes_hi[25] = XOR(lanes_hi[23], AND(NOT(lanes_hi[24]), lanes_hi[25])), XOR(lanes_hi[24], AND(NOT(lanes_hi[25]), lanes_hi[21])), XOR(lanes_hi[25], AND(NOT(lanes_hi[21]), lanes_hi[22])), XOR(lanes_hi[21], AND(NOT(lanes_hi[22]), lanes_hi[23])), XOR(lanes_hi[22], AND(NOT(lanes_hi[23]), lanes_hi[24]))
         end
      end
   end

end


if branch == "LJ" then


   -- SHA256 implementation for "LuaJIT without FFI" branch

   function sha256_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K = common_W, sha2_K_hi
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
         end
         for j = 17, 64 do
            local a, b = W[j-15], W[j-2]
            W[j] = NORM( NORM( XOR(ROR(a, 7), ROL(a, 14), SHR(a, 3)) + XOR(ROL(b, 15), ROL(b, 13), SHR(b, 10)) ) + NORM( W[j-7] + W[j-16] ) )
         end
         local a, b, c, d, e, f, g, h = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
         for j = 1, 64, 8 do  -- Thanks to Peter Cawley for this workaround (unroll the loop to avoid "PHI shuffling too complex" due to PHIs overlap)
            local z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j] + W[j] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+1] + W[j+1] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+2] + W[j+2] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+3] + W[j+3] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+4] + W[j+4] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+5] + W[j+5] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+6] + W[j+6] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
            z = NORM( XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + XOR(g, AND(e, XOR(f, g))) + (K[j+7] + W[j+7] + h) )
            h, g, f, e = g, f, e, NORM(d + z)
            d, c, b, a = c, b, a, NORM( XOR(AND(a, XOR(b, c)), AND(b, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10)) + z )
         end
         H[1], H[2], H[3], H[4] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4])
         H[5], H[6], H[7], H[8] = NORM(e + H[5]), NORM(f + H[6]), NORM(g + H[7]), NORM(h + H[8])
      end
   end

   local function ADD64_4(a_lo, a_hi, b_lo, b_hi, c_lo, c_hi, d_lo, d_hi)
      local sum_lo = a_lo % 2^32 + b_lo % 2^32 + c_lo % 2^32 + d_lo % 2^32
      local sum_hi = a_hi + b_hi + c_hi + d_hi
      local result_lo = NORM( sum_lo )
      local result_hi = NORM( sum_hi + floor(sum_lo / 2^32) )
      return result_lo, result_hi
   end

   if LuaJIT_arch == "x86" then  -- Special trick is required to avoid "PHI shuffling too complex" on x86 platform


      -- SHA512 implementation for "LuaJIT x86 without FFI" branch

      function sha512_feed_128(H_lo, H_hi, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 128
         -- W1_hi, W1_lo, W2_hi, W2_lo, ...   Wk_hi = W[2*k-1], Wk_lo = W[2*k]
         local W, K_lo, K_hi = common_W, sha2_K_lo, sha2_K_hi
         for pos = offs, offs + size - 1, 128 do
            for j = 1, 16*2 do
               pos = pos + 4
               local a, b, c, d = byte(str, pos - 3, pos)
               W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
            end
            for jj = 17*2, 80*2, 2 do
               local a_lo, a_hi = W[jj-30], W[jj-31]
               local t_lo = XOR(OR(SHR(a_lo, 1), SHL(a_hi, 31)), OR(SHR(a_lo, 8), SHL(a_hi, 24)), OR(SHR(a_lo, 7), SHL(a_hi, 25)))
               local t_hi = XOR(OR(SHR(a_hi, 1), SHL(a_lo, 31)), OR(SHR(a_hi, 8), SHL(a_lo, 24)), SHR(a_hi, 7))
               local b_lo, b_hi = W[jj-4], W[jj-5]
               local u_lo = XOR(OR(SHR(b_lo, 19), SHL(b_hi, 13)), OR(SHL(b_lo, 3), SHR(b_hi, 29)), OR(SHR(b_lo, 6), SHL(b_hi, 26)))
               local u_hi = XOR(OR(SHR(b_hi, 19), SHL(b_lo, 13)), OR(SHL(b_hi, 3), SHR(b_lo, 29)), SHR(b_hi, 6))
               W[jj], W[jj-1] = ADD64_4(t_lo, t_hi, u_lo, u_hi, W[jj-14], W[jj-15], W[jj-32], W[jj-33])
            end
            local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
            local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
            local zero = 0
            for j = 1, 80 do
               local t_lo = XOR(g_lo, AND(e_lo, XOR(f_lo, g_lo)))
               local t_hi = XOR(g_hi, AND(e_hi, XOR(f_hi, g_hi)))
               local u_lo = XOR(OR(SHR(e_lo, 14), SHL(e_hi, 18)), OR(SHR(e_lo, 18), SHL(e_hi, 14)), OR(SHL(e_lo, 23), SHR(e_hi, 9)))
               local u_hi = XOR(OR(SHR(e_hi, 14), SHL(e_lo, 18)), OR(SHR(e_hi, 18), SHL(e_lo, 14)), OR(SHL(e_hi, 23), SHR(e_lo, 9)))
               local sum_lo = u_lo % 2^32 + t_lo % 2^32 + h_lo % 2^32 + K_lo[j] + W[2*j] % 2^32
               local z_lo, z_hi = NORM( sum_lo ), NORM( u_hi + t_hi + h_hi + K_hi[j] + W[2*j-1] + floor(sum_lo / 2^32) )
               zero = zero + zero  -- this thick is needed to avoid "PHI shuffling too complex" due to PHIs overlap
               h_lo, h_hi, g_lo, g_hi, f_lo, f_hi = OR(zero, g_lo), OR(zero, g_hi), OR(zero, f_lo), OR(zero, f_hi), OR(zero, e_lo), OR(zero, e_hi)
               local sum_lo = z_lo % 2^32 + d_lo % 2^32
               e_lo, e_hi = NORM( sum_lo ), NORM( z_hi + d_hi + floor(sum_lo / 2^32) )
               d_lo, d_hi, c_lo, c_hi, b_lo, b_hi = OR(zero, c_lo), OR(zero, c_hi), OR(zero, b_lo), OR(zero, b_hi), OR(zero, a_lo), OR(zero, a_hi)
               u_lo = XOR(OR(SHR(b_lo, 28), SHL(b_hi, 4)), OR(SHL(b_lo, 30), SHR(b_hi, 2)), OR(SHL(b_lo, 25), SHR(b_hi, 7)))
               u_hi = XOR(OR(SHR(b_hi, 28), SHL(b_lo, 4)), OR(SHL(b_hi, 30), SHR(b_lo, 2)), OR(SHL(b_hi, 25), SHR(b_lo, 7)))
               t_lo = OR(AND(d_lo, c_lo), AND(b_lo, XOR(d_lo, c_lo)))
               t_hi = OR(AND(d_hi, c_hi), AND(b_hi, XOR(d_hi, c_hi)))
               local sum_lo = z_lo % 2^32 + t_lo % 2^32 + u_lo % 2^32
               a_lo, a_hi = NORM( sum_lo ), NORM( z_hi + t_hi + u_hi + floor(sum_lo / 2^32) )
            end
            H_lo[1], H_hi[1] = ADD64_4(H_lo[1], H_hi[1], a_lo, a_hi, 0, 0, 0, 0)
            H_lo[2], H_hi[2] = ADD64_4(H_lo[2], H_hi[2], b_lo, b_hi, 0, 0, 0, 0)
            H_lo[3], H_hi[3] = ADD64_4(H_lo[3], H_hi[3], c_lo, c_hi, 0, 0, 0, 0)
            H_lo[4], H_hi[4] = ADD64_4(H_lo[4], H_hi[4], d_lo, d_hi, 0, 0, 0, 0)
            H_lo[5], H_hi[5] = ADD64_4(H_lo[5], H_hi[5], e_lo, e_hi, 0, 0, 0, 0)
            H_lo[6], H_hi[6] = ADD64_4(H_lo[6], H_hi[6], f_lo, f_hi, 0, 0, 0, 0)
            H_lo[7], H_hi[7] = ADD64_4(H_lo[7], H_hi[7], g_lo, g_hi, 0, 0, 0, 0)
            H_lo[8], H_hi[8] = ADD64_4(H_lo[8], H_hi[8], h_lo, h_hi, 0, 0, 0, 0)
         end
      end

   else  -- all platforms except x86


      -- SHA512 implementation for "LuaJIT non-x86 without FFI" branch

      function sha512_feed_128(H_lo, H_hi, str, offs, size)
         -- offs >= 0, size >= 0, size is multiple of 128
         -- W1_hi, W1_lo, W2_hi, W2_lo, ...   Wk_hi = W[2*k-1], Wk_lo = W[2*k]
         local W, K_lo, K_hi = common_W, sha2_K_lo, sha2_K_hi
         for pos = offs, offs + size - 1, 128 do
            for j = 1, 16*2 do
               pos = pos + 4
               local a, b, c, d = byte(str, pos - 3, pos)
               W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
            end
            for jj = 17*2, 80*2, 2 do
               local a_lo, a_hi = W[jj-30], W[jj-31]
               local t_lo = XOR(OR(SHR(a_lo, 1), SHL(a_hi, 31)), OR(SHR(a_lo, 8), SHL(a_hi, 24)), OR(SHR(a_lo, 7), SHL(a_hi, 25)))
               local t_hi = XOR(OR(SHR(a_hi, 1), SHL(a_lo, 31)), OR(SHR(a_hi, 8), SHL(a_lo, 24)), SHR(a_hi, 7))
               local b_lo, b_hi = W[jj-4], W[jj-5]
               local u_lo = XOR(OR(SHR(b_lo, 19), SHL(b_hi, 13)), OR(SHL(b_lo, 3), SHR(b_hi, 29)), OR(SHR(b_lo, 6), SHL(b_hi, 26)))
               local u_hi = XOR(OR(SHR(b_hi, 19), SHL(b_lo, 13)), OR(SHL(b_hi, 3), SHR(b_lo, 29)), SHR(b_hi, 6))
               W[jj], W[jj-1] = ADD64_4(t_lo, t_hi, u_lo, u_hi, W[jj-14], W[jj-15], W[jj-32], W[jj-33])
            end
            local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
            local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
            for j = 1, 80 do
               local t_lo = XOR(g_lo, AND(e_lo, XOR(f_lo, g_lo)))
               local t_hi = XOR(g_hi, AND(e_hi, XOR(f_hi, g_hi)))
               local u_lo = XOR(OR(SHR(e_lo, 14), SHL(e_hi, 18)), OR(SHR(e_lo, 18), SHL(e_hi, 14)), OR(SHL(e_lo, 23), SHR(e_hi, 9)))
               local u_hi = XOR(OR(SHR(e_hi, 14), SHL(e_lo, 18)), OR(SHR(e_hi, 18), SHL(e_lo, 14)), OR(SHL(e_hi, 23), SHR(e_lo, 9)))
               local sum_lo = u_lo % 2^32 + t_lo % 2^32 + h_lo % 2^32 + K_lo[j] + W[2*j] % 2^32
               local z_lo, z_hi = NORM( sum_lo ), NORM( u_hi + t_hi + h_hi + K_hi[j] + W[2*j-1] + floor(sum_lo / 2^32) )
               h_lo, h_hi, g_lo, g_hi, f_lo, f_hi = g_lo, g_hi, f_lo, f_hi, e_lo, e_hi
               local sum_lo = z_lo % 2^32 + d_lo % 2^32
               e_lo, e_hi = NORM( sum_lo ), NORM( z_hi + d_hi + floor(sum_lo / 2^32) )
               d_lo, d_hi, c_lo, c_hi, b_lo, b_hi = c_lo, c_hi, b_lo, b_hi, a_lo, a_hi
               u_lo = XOR(OR(SHR(b_lo, 28), SHL(b_hi, 4)), OR(SHL(b_lo, 30), SHR(b_hi, 2)), OR(SHL(b_lo, 25), SHR(b_hi, 7)))
               u_hi = XOR(OR(SHR(b_hi, 28), SHL(b_lo, 4)), OR(SHL(b_hi, 30), SHR(b_lo, 2)), OR(SHL(b_hi, 25), SHR(b_lo, 7)))
               t_lo = OR(AND(d_lo, c_lo), AND(b_lo, XOR(d_lo, c_lo)))
               t_hi = OR(AND(d_hi, c_hi), AND(b_hi, XOR(d_hi, c_hi)))
               local sum_lo = z_lo % 2^32 + u_lo % 2^32 + t_lo % 2^32
               a_lo, a_hi = NORM( sum_lo ), NORM( z_hi + u_hi + t_hi + floor(sum_lo / 2^32) )
            end
            H_lo[1], H_hi[1] = ADD64_4(H_lo[1], H_hi[1], a_lo, a_hi, 0, 0, 0, 0)
            H_lo[2], H_hi[2] = ADD64_4(H_lo[2], H_hi[2], b_lo, b_hi, 0, 0, 0, 0)
            H_lo[3], H_hi[3] = ADD64_4(H_lo[3], H_hi[3], c_lo, c_hi, 0, 0, 0, 0)
            H_lo[4], H_hi[4] = ADD64_4(H_lo[4], H_hi[4], d_lo, d_hi, 0, 0, 0, 0)
            H_lo[5], H_hi[5] = ADD64_4(H_lo[5], H_hi[5], e_lo, e_hi, 0, 0, 0, 0)
            H_lo[6], H_hi[6] = ADD64_4(H_lo[6], H_hi[6], f_lo, f_hi, 0, 0, 0, 0)
            H_lo[7], H_hi[7] = ADD64_4(H_lo[7], H_hi[7], g_lo, g_hi, 0, 0, 0, 0)
            H_lo[8], H_hi[8] = ADD64_4(H_lo[8], H_hi[8], h_lo, h_hi, 0, 0, 0, 0)
         end
      end

   end


   -- MD5 implementation for "LuaJIT without FFI" branch

   function md5_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K = common_W, md5_K
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = OR(SHL(d, 24), SHL(c, 16), SHL(b, 8), a)
         end
         local a, b, c, d = H[1], H[2], H[3], H[4]
         for j = 1, 16, 4 do
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j  ] + W[j  ] + a),  7) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+1] + W[j+1] + a), 12) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+2] + W[j+2] + a), 17) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(d, AND(b, XOR(c, d))) + (K[j+3] + W[j+3] + a), 22) + b)
         end
         for j = 17, 32, 4 do
            local g = 5*j-4
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j  ] + W[AND(g     , 15) + 1] + a),  5) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+1] + W[AND(g +  5, 15) + 1] + a),  9) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+2] + W[AND(g + 10, 15) + 1] + a), 14) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, AND(d, XOR(b, c))) + (K[j+3] + W[AND(g -  1, 15) + 1] + a), 20) + b)
         end
         for j = 33, 48, 4 do
            local g = 3*j+2
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j  ] + W[AND(g    , 15) + 1] + a),  4) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+1] + W[AND(g + 3, 15) + 1] + a), 11) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+2] + W[AND(g + 6, 15) + 1] + a), 16) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(b, c, d) + (K[j+3] + W[AND(g - 7, 15) + 1] + a), 23) + b)
         end
         for j = 49, 64, 4 do
            local g = j*7
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j  ] + W[AND(g - 7, 15) + 1] + a),  6) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+1] + W[AND(g    , 15) + 1] + a), 10) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+2] + W[AND(g + 7, 15) + 1] + a), 15) + b)
            a, d, c, b = d, c, b, NORM(ROL(XOR(c, OR(b, NOT(d))) + (K[j+3] + W[AND(g - 2, 15) + 1] + a), 21) + b)
         end
         H[1], H[2], H[3], H[4] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4])
      end
   end


   -- SHA-1 implementation for "LuaJIT without FFI" branch

   function sha1_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W = common_W
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = OR(SHL(a, 24), SHL(b, 16), SHL(c, 8), d)
         end
         for j = 17, 80 do
            W[j] = ROL(XOR(W[j-3], W[j-8], W[j-14], W[j-16]), 1)
         end
         local a, b, c, d, e = H[1], H[2], H[3], H[4], H[5]
         for j = 1, 20, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j]   + 0x5A827999 + e))          -- constant = floor(2^30 * sqrt(2))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+1] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+2] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+3] + 0x5A827999 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(d, AND(b, XOR(d, c))) + (W[j+4] + 0x5A827999 + e))
         end
         for j = 21, 40, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j]   + 0x6ED9EBA1 + e))                       -- 2^30 * sqrt(3)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+1] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+2] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+3] + 0x6ED9EBA1 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+4] + 0x6ED9EBA1 + e))
         end
         for j = 41, 60, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j]   + 0x8F1BBCDC + e))  -- 2^30 * sqrt(5)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+1] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+2] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+3] + 0x8F1BBCDC + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(AND(d, XOR(b, c)), AND(b, c)) + (W[j+4] + 0x8F1BBCDC + e))
         end
         for j = 61, 80, 5 do
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j]   + 0xCA62C1D6 + e))                       -- 2^30 * sqrt(10)
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+1] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+2] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+3] + 0xCA62C1D6 + e))
            e, d, c, b, a = d, c, ROR(b, 2), a, NORM(ROL(a, 5) + XOR(b, c, d) + (W[j+4] + 0xCA62C1D6 + e))
         end
         H[1], H[2], H[3], H[4], H[5] = NORM(a + H[1]), NORM(b + H[2]), NORM(c + H[3]), NORM(d + H[4]), NORM(e + H[5])
      end
   end

end


if branch == "INT64" then


   -- implementation for Lua 5.3/5.4

   hi_factor = 4294967296
   hi_factor_keccak = 4294967296
   lanes_index_base = 1

   HEX64, XOR64A5, XOR_BYTE, sha256_feed_64, sha512_feed_128, md5_feed_64, sha1_feed_64, keccak_feed = load[[local a,b,c,d,e,f=...local g,h=string.format,string.unpack;local function i(j)return g("%016x",j)end;local function k(j)return j~0xa5a5a5a5a5a5a5a5 end;local function l(j,m)return j~m end;local n={}local function o(p,q,r,s)local t,u=n,d;local v,w,x,y,z,A,B,C=p[1],p[2],p[3],p[4],p[5],p[6],p[7],p[8]for D=r+1,r+s,64 do t[1],t[2],t[3],t[4],t[5],t[6],t[7],t[8],t[9],t[10],t[11],t[12],t[13],t[14],t[15],t[16]=h(">I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4",q,D)for E=17,64 do local F=t[E-15]F=F<<32|F;local G=t[E-2]G=G<<32|G;t[E]=F>>7~(F>>18)~(F>>35)+G>>17~(G>>19)~(G>>42)+t[E-7]+t[E-16]&1<<32-1 end;local F,G,H,I,J,K,L,M=v,w,x,y,z,A,B,C;for E=1,64 do J=J<<32|(J&1<<32-1)local N=J>>6~(J>>11)~(J>>25)+L~(J&(K~L))+M+u[E]+t[E]M=L;L=K;K=J;J=N+I;I=H;H=G;G=F;F=F<<32|(F&1<<32-1)F=N+F~H&I~(F&H)+F>>2~(F>>13)~(F>>22)end;v=F+v;w=G+w;x=H+x;y=I+y;z=J+z;A=K+A;B=L+B;C=M+C end;p[1],p[2],p[3],p[4],p[5],p[6],p[7],p[8]=v,w,x,y,z,A,B,C end;local function O(p,P,q,r,s)local t,u=n,c;local v,w,x,y,z,A,B,C=p[1],p[2],p[3],p[4],p[5],p[6],p[7],p[8]for D=r+1,r+s,128 do t[1],t[2],t[3],t[4],t[5],t[6],t[7],t[8],t[9],t[10],t[11],t[12],t[13],t[14],t[15],t[16]=h(">i8i8i8i8i8i8i8i8i8i8i8i8i8i8i8i8",q,D)for E=17,80 do local F=t[E-15]local G=t[E-2]t[E]=F>>1~(F>>7)~(F>>8)~(F<<56)~(F<<63)+G>>6~(G>>19)~(G>>61)~(G<<3)~(G<<45)+t[E-7]+t[E-16]end;local F,G,H,I,J,K,L,M=v,w,x,y,z,A,B,C;for E=1,80 do local N=J>>14~(J>>18)~(J>>41)~(J<<23)~(J<<46)~(J<<50)+L~(J&(K~L))+M+u[E]+t[E]M=L;L=K;K=J;J=N+I;I=H;H=G;G=F;F=N+F~H&I~(F&H)+F>>28~(F>>34)~(F>>39)~(F<<25)~(F<<30)~(F<<36)end;v=F+v;w=G+w;x=H+x;y=I+y;z=J+z;A=K+A;B=L+B;C=M+C end;p[1],p[2],p[3],p[4],p[5],p[6],p[7],p[8]=v,w,x,y,z,A,B,C end;local function Q(p,q,r,s)local t,u,a=n,b,a;local v,w,x,y=p[1],p[2],p[3],p[4]for D=r+1,r+s,64 do t[1],t[2],t[3],t[4],t[5],t[6],t[7],t[8],t[9],t[10],t[11],t[12],t[13],t[14],t[15],t[16]=h("<I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4",q,D)local F,G,H,I=v,w,x,y;local R=32-7;for E=1,16 do local S=I~(G&(H~I))+F+u[E]+t[E]F=I;I=H;H=G;G=S<<32|(S&1<<32-1)>>R+G;R=a[R]end;R=32-5;for E=17,32 do local S=H~(I&(G~H))+F+u[E]+t[5*E-4&15+1]F=I;I=H;H=G;G=S<<32|(S&1<<32-1)>>R+G;R=a[R]end;R=32-4;for E=33,48 do local S=G~H~I+F+u[E]+t[3*E+2&15+1]F=I;I=H;H=G;G=S<<32|(S&1<<32-1)>>R+G;R=a[R]end;R=32-6;for E=49,64 do local S=H~(G|~I)+F+u[E]+t[E*7-7&15+1]F=I;I=H;H=G;G=S<<32|(S&1<<32-1)>>R+G;R=a[R]end;v=F+v;w=G+w;x=H+x;y=I+y end;p[1],p[2],p[3],p[4]=v,w,x,y end;local function T(p,q,r,s)local t=n;local v,w,x,y,z=p[1],p[2],p[3],p[4],p[5]for D=r+1,r+s,64 do t[1],t[2],t[3],t[4],t[5],t[6],t[7],t[8],t[9],t[10],t[11],t[12],t[13],t[14],t[15],t[16]=h(">I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4I4",q,D)for E=17,80 do local F=t[E-3]~t[E-8]~t[E-14]~t[E-16]t[E]=F<<32|F<<1>>32 end;local F,G,H,I,J=v,w,x,y,z;for E=1,20 do local N=F<<32|(F&1<<32-1)>>27+I~(G&(H~I))+0x5A827999+t[E]+J;J=I;I=H;H=G<<32|(G&1<<32-1)>>2;G=F;F=N end;for E=21,40 do local N=F<<32|(F&1<<32-1)>>27+G~H~I+0x6ED9EBA1+t[E]+J;J=I;I=H;H=G<<32|(G&1<<32-1)>>2;G=F;F=N end;for E=41,60 do local N=F<<32|(F&1<<32-1)>>27+G~H&I~(G&H)+0x8F1BBCDC+t[E]+J;J=I;I=H;H=G<<32|(G&1<<32-1)>>2;G=F;F=N end;for E=61,80 do local N=F<<32|(F&1<<32-1)>>27+G~H~I+0xCA62C1D6+t[E]+J;J=I;I=H;H=G<<32|(G&1<<32-1)>>2;G=F;F=N end;v=F+v;w=G+w;x=H+x;y=I+y;z=J+z end;p[1],p[2],p[3],p[4],p[5]=v,w,x,y,z end;local U=e("i8")local function V(W,P,q,r,s,X)local Y=f;local Z=X/8;local _=U[Z]for D=r+1,r+s,X do local a0={h(_,q,D)}for E=1,Z do W[E]=W[E]~a0[E]end;local a1,a2,a3,a4,a5,a6,a7,a8,a9,aa,ab,ac,ad,ae,af,ag,ah,ai,aj,ak,al,am,an,ao,ap=W[1],W[2],W[3],W[4],W[5],W[6],W[7],W[8],W[9],W[10],W[11],W[12],W[13],W[14],W[15],W[16],W[17],W[18],W[19],W[20],W[21],W[22],W[23],W[24],W[25]for aq=1,24 do local ar=a1~a6~ab~ag~al;local as=a2~a7~ac~ah~am;local at=a3~a8~ad~ai~an;local au=a4~a9~ae~aj~ao;local av=a5~aa~af~ak~ap;local aw=ar~(at<<1)~(at>>63)local ax=aw~a2;local ay=aw~a7;local az=aw~ac;local aA=aw~ah;local aB=aw~am;a2=ay<<44~(ay>>20)a7=aA<<45~(aA>>19)ac=ax<<1~(ax>>63)ah=az<<10~(az>>54)am=aB<<2~(aB>>62)aw=as~(au<<1)~(au>>63)ax=aw~a3;ay=aw~a8;az=aw~ad;aA=aw~ai;aB=aw~an;a3=az<<43~(az>>21)a8=aB<<61~(aB>>3)ad=ay<<6~(ay>>58)ai=aA<<15~(aA>>49)an=ax<<62~(ax>>2)aw=at~(av<<1)~(av>>63)ax=aw~a4;ay=aw~a9;az=aw~ae;aA=aw~aj;aB=aw~ao;a4=aA<<21~(aA>>43)a9=ax<<28~(ax>>36)ae=az<<25~(az>>39)aj=aB<<56~(aB>>8)ao=ay<<55~(ay>>9)aw=au~(ar<<1)~(ar>>63)ax=aw~a5;ay=aw~aa;az=aw~af;aA=aw~ak;aB=aw~ap;a5=aB<<14~(aB>>50)aa=ay<<20~(ay>>44)af=aA<<8~(aA>>56)ak=ax<<27~(ax>>37)ap=az<<39~(az>>25)aw=av~(as<<1)~(as>>63)ay=aw~a6;az=aw~ab;aA=aw~ag;aB=aw~al;a6=az<<3~(az>>61)ab=aB<<18~(aB>>46)ag=ay<<36~(ay>>28)al=aA<<41~(aA>>23)a1=aw~a1;a1,a2,a3,a4,a5=a1~(~a2&a3),a2~(~a3&a4),a3~(~a4&a5),a4~(~a5&a1),a5~(~a1&a2)a6,a7,a8,a9,aa=a9~(~aa&a6),aa~(~a6&a7),a6~(~a7&a8),a7~(~a8&a9),a8~(~a9&aa)ab,ac,ad,ae,af=ac~(~ad&ae),ad~(~ae&af),ae~(~af&ab),af~(~ab&ac),ab~(~ac&ad)ag,ah,ai,aj,ak=ak~(~ag&ah),ag~(~ah&ai),ah~(~ai&aj),ai~(~aj&ak),aj~(~ak&ag)al,am,an,ao,ap=an~(~ao&ap),ao~(~ap&al),ap~(~al&am),al~(~am&an),am~(~an&ao)a1=a1~Y[aq]end;W[1]=a1;W[2]=a2;W[3]=a3;W[4]=a4;W[5]=a5;W[6]=a6;W[7]=a7;W[8]=a8;W[9]=a9;W[10]=aa;W[11]=ab;W[12]=ac;W[13]=ad;W[14]=ae;W[15]=af;W[16]=ag;W[17]=ah;W[18]=ai;W[19]=aj;W[20]=ak;W[21]=al;W[22]=am;W[23]=an;W[24]=ao;W[25]=ap end end;return i,k,l,o,O,Q,T,V]](md5_next_shift, md5_K, sha2_K_lo, sha2_K_hi, build_keccak_format, sha3_RC_lo)

end


if branch == "INT32" then


   -- implementation for Lua 5.3/5.4 having non-standard numbers config "int32"+"double" (built with LUA_INT_TYPE=LUA_INT_INT)

   K_lo_modulo = 2^32

   function HEX(x) -- returns string of 8 lowercase hexadecimal digits
      return string_format("%08x", x)
   end

   XOR32A5, XOR_BYTE, sha256_feed_64, sha512_feed_128, md5_feed_64, sha1_feed_64, keccak_feed = load[[local a,b,c,d,e,f,g=...local h,i=string.unpack,math.floor;local function j(k)return k~0xA5A5A5A5 end;local function l(k,m)return k~m end;local n={}local function o(p,q,r,s)local t,u=n,d;local v,w,x,y,z,A,B,C=p[1],p[2],p[3],p[4],p[5],p[6],p[7],p[8]for D=r+1,r+s,64 do t[1],t[2],t[3],t[4],t[5],t[6],t[7],t[8],t[9],t[10],t[11],t[12],t[13],t[14],t[15],t[16]=h(">i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4",q,D)for E=17,64 do local F,G=t[E-15],t[E-2]t[E]=F>>7~(F<<25)~(F<<14)~(F>>18)~(F>>3)+G<<15~(G>>17)~(G<<13)~(G>>19)~(G>>10)+t[E-7]+t[E-16]end;local F,G,H,I,J,K,L,M=v,w,x,y,z,A,B,C;for E=1,64 do local N=J>>6~(J<<26)~(J>>11)~(J<<21)~(J>>25)~(J<<7)+L~(J&(K~L))+M+u[E]+t[E]M=L;L=K;K=J;J=N+I;I=H;H=G;G=F;F=N+F~H&I~(F&H)+F>>2~(F<<30)~(F>>13)~(F<<19)~(F<<10)~(F>>22)end;v=F+v;w=G+w;x=H+x;y=I+y;z=J+z;A=K+A;B=L+B;C=M+C end;p[1],p[2],p[3],p[4],p[5],p[6],p[7],p[8]=v,w,x,y,z,A,B,C end;local function O(P,Q,q,r,s)local i,t,R,S=i,n,c,d;local T,U,V,W,X,Y,Z,_=P[1],P[2],P[3],P[4],P[5],P[6],P[7],P[8]local a0,a1,a2,a3,a4,a5,a6,a7=Q[1],Q[2],Q[3],Q[4],Q[5],Q[6],Q[7],Q[8]for D=r+1,r+s,128 do t[1],t[2],t[3],t[4],t[5],t[6],t[7],t[8],t[9],t[10],t[11],t[12],t[13],t[14],t[15],t[16],t[17],t[18],t[19],t[20],t[21],t[22],t[23],t[24],t[25],t[26],t[27],t[28],t[29],t[30],t[31],t[32]=h(">i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4",q,D)for a8=17*2,80*2,2 do local a9,aa,ab,ac=t[a8-30],t[a8-31],t[a8-4],t[a8-5]local ad=a9>>1~(aa<<31)~(a9>>8)~(aa<<24)~(a9>>7)~(aa<<25)%2^32+ab>>19~(ac<<13)~(ab<<3)~(ac>>29)~(ab>>6)~(ac<<26)%2^32+t[a8-14]%2^32+t[a8-32]%2^32;t[a8-1]=aa>>1~(a9<<31)~(aa>>8)~(a9<<24)~(aa>>7)+ac>>19~(ab<<13)~(ac<<3)~(ab>>29)~(ac>>6)+t[a8-15]+t[a8-33]+i(ad/2^32)t[a8]=0|(ad+2^31)%2^32-2^31 end;local a9,ab,ae,af,ag,ah,ai,aj=T,U,V,W,X,Y,Z,_;local aa,ac,ak,al,am,an,ao,ap=a0,a1,a2,a3,a4,a5,a6,a7;for E=1,80 do local a8=2*E;local aq=ag>>14~(am<<18)~(ag>>18)~(am<<14)~(ag<<23)~(am>>9)%2^32+ai~(ag&(ah~ai))%2^32+aj%2^32+R[E]+t[a8]%2^32;local ar=am>>14~(ag<<18)~(am>>18)~(ag<<14)~(am<<23)~(ag>>9)+ao~(am&(an~ao))+ap+S[E]+t[a8-1]+i(aq/2^32)aq=aq%2^32;aj=ai;ap=ao;ai=ah;ao=an;ah=ag;an=am;ag=aq+af%2^32;am=ar+al+i(ag/2^32)ag=0|(ag+2^31)%2^32-2^31;af=ae;al=ak;ae=ab;ak=ac;ab=a9;ac=aa;aq=aq+af&ae~(ab&(af~ae))%2^32+ab>>28~(ac<<4)~(ab<<30)~(ac>>2)~(ab<<25)~(ac>>7)%2^32;aa=ar+al&ak~(ac&(al~ak))+ac>>28~(ab<<4)~(ac<<30)~(ab>>2)~(ac<<25)~(ab>>7)+i(aq/2^32)a9=0|(aq+2^31)%2^32-2^31 end;a9=T%2^32+a9%2^32;a0=a0+aa+i(a9/2^32)T=0|(a9+2^31)%2^32-2^31;a9=U%2^32+ab%2^32;a1=a1+ac+i(a9/2^32)U=0|(a9+2^31)%2^32-2^31;a9=V%2^32+ae%2^32;a2=a2+ak+i(a9/2^32)V=0|(a9+2^31)%2^32-2^31;a9=W%2^32+af%2^32;a3=a3+al+i(a9/2^32)W=0|(a9+2^31)%2^32-2^31;a9=X%2^32+ag%2^32;a4=a4+am+i(a9/2^32)X=0|(a9+2^31)%2^32-2^31;a9=Y%2^32+ah%2^32;a5=a5+an+i(a9/2^32)Y=0|(a9+2^31)%2^32-2^31;a9=Z%2^32+ai%2^32;a6=a6+ao+i(a9/2^32)Z=0|(a9+2^31)%2^32-2^31;a9=_%2^32+aj%2^32;a7=a7+ap+i(a9/2^32)_=0|(a9+2^31)%2^32-2^31 end;P[1],P[2],P[3],P[4],P[5],P[6],P[7],P[8]=T,U,V,W,X,Y,Z,_;Q[1],Q[2],Q[3],Q[4],Q[5],Q[6],Q[7],Q[8]=a0,a1,a2,a3,a4,a5,a6,a7 end;local function as(p,q,r,s)local t,u,a=n,b,a;local v,w,x,y=p[1],p[2],p[3],p[4]for D=r+1,r+s,64 do t[1],t[2],t[3],t[4],t[5],t[6],t[7],t[8],t[9],t[10],t[11],t[12],t[13],t[14],t[15],t[16]=h("<i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4",q,D)local F,G,H,I=v,w,x,y;local at=32-7;for E=1,16 do local au=I~(G&(H~I))+F+u[E]+t[E]F=I;I=H;H=G;G=au<<32-at|(au>>at)+G;at=a[at]end;at=32-5;for E=17,32 do local au=H~(I&(G~H))+F+u[E]+t[5*E-4&15+1]F=I;I=H;H=G;G=au<<32-at|(au>>at)+G;at=a[at]end;at=32-4;for E=33,48 do local au=G~H~I+F+u[E]+t[3*E+2&15+1]F=I;I=H;H=G;G=au<<32-at|(au>>at)+G;at=a[at]end;at=32-6;for E=49,64 do local au=H~(G|~I)+F+u[E]+t[E*7-7&15+1]F=I;I=H;H=G;G=au<<32-at|(au>>at)+G;at=a[at]end;v=F+v;w=G+w;x=H+x;y=I+y end;p[1],p[2],p[3],p[4]=v,w,x,y end;local function av(p,q,r,s)local t=n;local v,w,x,y,z=p[1],p[2],p[3],p[4],p[5]for D=r+1,r+s,64 do t[1],t[2],t[3],t[4],t[5],t[6],t[7],t[8],t[9],t[10],t[11],t[12],t[13],t[14],t[15],t[16]=h(">i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4i4",q,D)for E=17,80 do local F=t[E-3]~t[E-8]~t[E-14]~t[E-16]t[E]=F<<1~(F>>31)end;local F,G,H,I,J=v,w,x,y,z;for E=1,20 do local N=F<<5~(F>>27)+I~(G&(H~I))+0x5A827999+t[E]+J;J=I;I=H;H=G<<30~(G>>2)G=F;F=N end;for E=21,40 do local N=F<<5~(F>>27)+G~H~I+0x6ED9EBA1+t[E]+J;J=I;I=H;H=G<<30~(G>>2)G=F;F=N end;for E=41,60 do local N=F<<5~(F>>27)+G~H&I~(G&H)+0x8F1BBCDC+t[E]+J;J=I;I=H;H=G<<30~(G>>2)G=F;F=N end;for E=61,80 do local N=F<<5~(F>>27)+G~H~I+0xCA62C1D6+t[E]+J;J=I;I=H;H=G<<30~(G>>2)G=F;F=N end;v=F+v;w=G+w;x=H+x;y=I+y;z=J+z end;p[1],p[2],p[3],p[4],p[5]=v,w,x,y,z end;local aw=e("i4i4")local function ax(ay,az,q,r,s,aA)local aB,aC=f,g;local aD=aA/8;local aE=aw[aD]for D=r+1,r+s,aA do local aF={h(aE,q,D)}for E=1,aD do ay[E]=ay[E]~aF[2*E-1]az[E]=az[E]~aF[2*E]end;local aG,aH,aI,aJ,aK,aL,aM,aN,aO,aP,aQ,aR,aS,aT,aU,aV,aW,aX,aY,aZ,a_,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,ba,bb,bc,bd,be,bf,bg,bh,bi,bj,bk,bl,bm,bn,bo,bp,bq,br,bs=ay[1],az[1],ay[2],az[2],ay[3],az[3],ay[4],az[4],ay[5],az[5],ay[6],az[6],ay[7],az[7],ay[8],az[8],ay[9],az[9],ay[10],az[10],ay[11],az[11],ay[12],az[12],ay[13],az[13],ay[14],az[14],ay[15],az[15],ay[16],az[16],ay[17],az[17],ay[18],az[18],ay[19],az[19],ay[20],az[20],ay[21],az[21],ay[22],az[22],ay[23],az[23],ay[24],az[24],ay[25],az[25]for bt=1,24 do local bu=aG~aQ~a_~b9~bj;local bv=aH~aR~b0~ba~bk;local bw=aI~aS~b1~bb~bl;local bx=aJ~aT~b2~bc~bm;local by=aK~aU~b3~bd~bn;local bz=aL~aV~b4~be~bo;local bA=aM~aW~b5~bf~bp;local bB=aN~aX~b6~bg~bq;local bC=aO~aY~b7~bh~br;local bD=aP~aZ~b8~bi~bs;local bE=bu~(by<<1)~(bz>>31)local bF=bv~(bz<<1)~(by>>31)local bG=bE~aI;local bH=bF~aJ;local bI=bE~aS;local bJ=bF~aT;local bK=bE~b1;local bL=bF~b2;local bM=bE~bb;local bN=bF~bc;local bO=bE~bl;local bP=bF~bm;aI=bI>>20~(bJ<<12)aJ=bJ>>20~(bI<<12)aS=bM>>19~(bN<<13)aT=bN>>19~(bM<<13)b1=bG<<1~(bH>>31)b2=bH<<1~(bG>>31)bb=bK<<10~(bL>>22)bc=bL<<10~(bK>>22)bl=bO<<2~(bP>>30)bm=bP<<2~(bO>>30)bE=bw~(bA<<1)~(bB>>31)bF=bx~(bB<<1)~(bA>>31)bG=bE~aK;bH=bF~aL;bI=bE~aU;bJ=bF~aV;bK=bE~b3;bL=bF~b4;bM=bE~bd;bN=bF~be;bO=bE~bn;bP=bF~bo;aK=bK>>21~(bL<<11)aL=bL>>21~(bK<<11)aU=bO>>3~(bP<<29)aV=bP>>3~(bO<<29)b3=bI<<6~(bJ>>26)b4=bJ<<6~(bI>>26)bd=bM<<15~(bN>>17)be=bN<<15~(bM>>17)bn=bG>>2~(bH<<30)bo=bH>>2~(bG<<30)bE=by~(bC<<1)~(bD>>31)bF=bz~(bD<<1)~(bC>>31)bG=bE~aM;bH=bF~aN;bI=bE~aW;bJ=bF~aX;bK=bE~b5;bL=bF~b6;bM=bE~bf;bN=bF~bg;bO=bE~bp;bP=bF~bq;aM=bM<<21~(bN>>11)aN=bN<<21~(bM>>11)aW=bG<<28~(bH>>4)aX=bH<<28~(bG>>4)b5=bK<<25~(bL>>7)b6=bL<<25~(bK>>7)bf=bO>>8~(bP<<24)bg=bP>>8~(bO<<24)bp=bI>>9~(bJ<<23)bq=bJ>>9~(bI<<23)bE=bA~(bu<<1)~(bv>>31)bF=bB~(bv<<1)~(bu>>31)bG=bE~aO;bH=bF~aP;bI=bE~aY;bJ=bF~aZ;bK=bE~b7;bL=bF~b8;bM=bE~bh;bN=bF~bi;bO=bE~br;bP=bF~bs;aO=bO<<14~(bP>>18)aP=bP<<14~(bO>>18)aY=bI<<20~(bJ>>12)aZ=bJ<<20~(bI>>12)b7=bM<<8~(bN>>24)b8=bN<<8~(bM>>24)bh=bG<<27~(bH>>5)bi=bH<<27~(bG>>5)br=bK>>25~(bL<<7)bs=bL>>25~(bK<<7)bE=bC~(bw<<1)~(bx>>31)bF=bD~(bx<<1)~(bw>>31)bI=bE~aQ;bJ=bF~aR;bK=bE~a_;bL=bF~b0;bM=bE~b9;bN=bF~ba;bO=bE~bj;bP=bF~bk;aQ=bK<<3~(bL>>29)aR=bL<<3~(bK>>29)a_=bO<<18~(bP>>14)b0=bP<<18~(bO>>14)b9=bI>>28~(bJ<<4)ba=bJ>>28~(bI<<4)bj=bM>>23~(bN<<9)bk=bN>>23~(bM<<9)aG=bE~aG;aH=bF~aH;aG,aI,aK,aM,aO=aG~(~aI&aK),aI~(~aK&aM),aK~(~aM&aO),aM~(~aO&aG),aO~(~aG&aI)aH,aJ,aL,aN,aP=aH~(~aJ&aL),aJ~(~aL&aN),aL~(~aN&aP),aN~(~aP&aH),aP~(~aH&aJ)aQ,aS,aU,aW,aY=aW~(~aY&aQ),aY~(~aQ&aS),aQ~(~aS&aU),aS~(~aU&aW),aU~(~aW&aY)aR,aT,aV,aX,aZ=aX~(~aZ&aR),aZ~(~aR&aT),aR~(~aT&aV),aT~(~aV&aX),aV~(~aX&aZ)a_,b1,b3,b5,b7=b1~(~b3&b5),b3~(~b5&b7),b5~(~b7&a_),b7~(~a_&b1),a_~(~b1&b3)b0,b2,b4,b6,b8=b2~(~b4&b6),b4~(~b6&b8),b6~(~b8&b0),b8~(~b0&b2),b0~(~b2&b4)b9,bb,bd,bf,bh=bh~(~b9&bb),b9~(~bb&bd),bb~(~bd&bf),bd~(~bf&bh),bf~(~bh&b9)ba,bc,be,bg,bi=bi~(~ba&bc),ba~(~bc&be),bc~(~be&bg),be~(~bg&bi),bg~(~bi&ba)bj,bl,bn,bp,br=bn~(~bp&br),bp~(~br&bj),br~(~bj&bl),bj~(~bl&bn),bl~(~bn&bp)bk,bm,bo,bq,bs=bo~(~bq&bs),bq~(~bs&bk),bs~(~bk&bm),bk~(~bm&bo),bm~(~bo&bq)aG=aG~aB[bt]aH=aH~aC[bt]end;ay[1]=aG;az[1]=aH;ay[2]=aI;az[2]=aJ;ay[3]=aK;az[3]=aL;ay[4]=aM;az[4]=aN;ay[5]=aO;az[5]=aP;ay[6]=aQ;az[6]=aR;ay[7]=aS;az[7]=aT;ay[8]=aU;az[8]=aV;ay[9]=aW;az[9]=aX;ay[10]=aY;az[10]=aZ;ay[11]=a_;az[11]=b0;ay[12]=b1;az[12]=b2;ay[13]=b3;az[13]=b4;ay[14]=b5;az[14]=b6;ay[15]=b7;az[15]=b8;ay[16]=b9;az[16]=ba;ay[17]=bb;az[17]=bc;ay[18]=bd;az[18]=be;ay[19]=bf;az[19]=bg;ay[20]=bh;az[20]=bi;ay[21]=bj;az[21]=bk;ay[22]=bl;az[22]=bm;ay[23]=bn;az[23]=bo;ay[24]=bp;az[24]=bq;ay[25]=br;az[25]=bs end end;return j,l,o,O,as,av,ax]](md5_next_shift, md5_K, sha2_K_lo, sha2_K_hi, build_keccak_format, sha3_RC_lo, sha3_RC_hi)

end


if branch == "LIB32" or branch == "EMUL" then


   -- implementation for Lua 5.1/5.2 (with or without bitwise library available)

   function sha256_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K = common_W, sha2_K_hi
      local h1, h2, h3, h4, h5, h6, h7, h8 = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = ((a * 256 + b) * 256 + c) * 256 + d
         end
         for j = 17, 64 do
            local a, b = W[j-15], W[j-2]
            W[j] = XOR(ROR(a, 7), ROL(a, 14), SHR(a, 3)) + XOR(ROL(b, 15), ROL(b, 13), SHR(b, 10)) + W[j-7] + W[j-16]
         end
         local a, b, c, d, e, f, g, h = h1, h2, h3, h4, h5, h6, h7, h8
         for j = 1, 64 do
            local z = XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + AND(e, f) + AND(-1-e, g) + h + K[j] + W[j]
            h = g
            g = f
            f = e
            e = z + d
            d = c
            c = b
            b = a
            a = z + AND(d, c) + AND(a, XOR(d, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10))
         end
         h1, h2, h3, h4 = (a + h1) % 4294967296, (b + h2) % 4294967296, (c + h3) % 4294967296, (d + h4) % 4294967296
         h5, h6, h7, h8 = (e + h5) % 4294967296, (f + h6) % 4294967296, (g + h7) % 4294967296, (h + h8) % 4294967296
      end
      H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8] = h1, h2, h3, h4, h5, h6, h7, h8
   end

   function sha512_feed_128(H_lo, H_hi, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 128
      -- W1_hi, W1_lo, W2_hi, W2_lo, ...   Wk_hi = W[2*k-1], Wk_lo = W[2*k]
      local W, K_lo, K_hi = common_W, sha2_K_lo, sha2_K_hi
      local h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
      local h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
      for pos = offs, offs + size - 1, 128 do
         for j = 1, 16*2 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = ((a * 256 + b) * 256 + c) * 256 + d
         end
         for jj = 17*2, 80*2, 2 do
            local a_lo, a_hi, b_lo, b_hi = W[jj-30], W[jj-31], W[jj-4], W[jj-5]
            local tmp1 = XOR(SHR(a_lo, 1) + SHL(a_hi, 31), SHR(a_lo, 8) + SHL(a_hi, 24), SHR(a_lo, 7) + SHL(a_hi, 25)) % 4294967296 + XOR(SHR(b_lo, 19) + SHL(b_hi, 13), SHL(b_lo, 3) + SHR(b_hi, 29), SHR(b_lo, 6) + SHL(b_hi, 26)) % 4294967296 + W[jj-14] + W[jj-32]
            local tmp2 = tmp1 % 4294967296
            W[jj-1] = XOR(SHR(a_hi, 1) + SHL(a_lo, 31), SHR(a_hi, 8) + SHL(a_lo, 24), SHR(a_hi, 7)) + XOR(SHR(b_hi, 19) + SHL(b_lo, 13), SHL(b_hi, 3) + SHR(b_lo, 29), SHR(b_hi, 6)) + W[jj-15] + W[jj-33] + (tmp1 - tmp2) / 4294967296
            W[jj] = tmp2
         end
         local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
         local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
         for j = 1, 80 do
            local jj = 2*j
            local tmp1 = XOR(SHR(e_lo, 14) + SHL(e_hi, 18), SHR(e_lo, 18) + SHL(e_hi, 14), SHL(e_lo, 23) + SHR(e_hi, 9)) % 4294967296 + (AND(e_lo, f_lo) + AND(-1-e_lo, g_lo)) % 4294967296 + h_lo + K_lo[j] + W[jj]
            local z_lo = tmp1 % 4294967296
            local z_hi = XOR(SHR(e_hi, 14) + SHL(e_lo, 18), SHR(e_hi, 18) + SHL(e_lo, 14), SHL(e_hi, 23) + SHR(e_lo, 9)) + AND(e_hi, f_hi) + AND(-1-e_hi, g_hi) + h_hi + K_hi[j] + W[jj-1] + (tmp1 - z_lo) / 4294967296
            h_lo = g_lo
            h_hi = g_hi
            g_lo = f_lo
            g_hi = f_hi
            f_lo = e_lo
            f_hi = e_hi
            tmp1 = z_lo + d_lo
            e_lo = tmp1 % 4294967296
            e_hi = z_hi + d_hi + (tmp1 - e_lo) / 4294967296
            d_lo = c_lo
            d_hi = c_hi
            c_lo = b_lo
            c_hi = b_hi
            b_lo = a_lo
            b_hi = a_hi
            tmp1 = z_lo + (AND(d_lo, c_lo) + AND(b_lo, XOR(d_lo, c_lo))) % 4294967296 + XOR(SHR(b_lo, 28) + SHL(b_hi, 4), SHL(b_lo, 30) + SHR(b_hi, 2), SHL(b_lo, 25) + SHR(b_hi, 7)) % 4294967296
            a_lo = tmp1 % 4294967296
            a_hi = z_hi + (AND(d_hi, c_hi) + AND(b_hi, XOR(d_hi, c_hi))) + XOR(SHR(b_hi, 28) + SHL(b_lo, 4), SHL(b_hi, 30) + SHR(b_lo, 2), SHL(b_hi, 25) + SHR(b_lo, 7)) + (tmp1 - a_lo) / 4294967296
         end
         a_lo = h1_lo + a_lo
         h1_lo = a_lo % 4294967296
         h1_hi = (h1_hi + a_hi + (a_lo - h1_lo) / 4294967296) % 4294967296
         a_lo = h2_lo + b_lo
         h2_lo = a_lo % 4294967296
         h2_hi = (h2_hi + b_hi + (a_lo - h2_lo) / 4294967296) % 4294967296
         a_lo = h3_lo + c_lo
         h3_lo = a_lo % 4294967296
         h3_hi = (h3_hi + c_hi + (a_lo - h3_lo) / 4294967296) % 4294967296
         a_lo = h4_lo + d_lo
         h4_lo = a_lo % 4294967296
         h4_hi = (h4_hi + d_hi + (a_lo - h4_lo) / 4294967296) % 4294967296
         a_lo = h5_lo + e_lo
         h5_lo = a_lo % 4294967296
         h5_hi = (h5_hi + e_hi + (a_lo - h5_lo) / 4294967296) % 4294967296
         a_lo = h6_lo + f_lo
         h6_lo = a_lo % 4294967296
         h6_hi = (h6_hi + f_hi + (a_lo - h6_lo) / 4294967296) % 4294967296
         a_lo = h7_lo + g_lo
         h7_lo = a_lo % 4294967296
         h7_hi = (h7_hi + g_hi + (a_lo - h7_lo) / 4294967296) % 4294967296
         a_lo = h8_lo + h_lo
         h8_lo = a_lo % 4294967296
         h8_hi = (h8_hi + h_hi + (a_lo - h8_lo) / 4294967296) % 4294967296
      end
      H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8] = h1_lo, h2_lo, h3_lo, h4_lo, h5_lo, h6_lo, h7_lo, h8_lo
      H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8] = h1_hi, h2_hi, h3_hi, h4_hi, h5_hi, h6_hi, h7_hi, h8_hi
   end

   function md5_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W, K, md5_next_shift = common_W, md5_K, md5_next_shift
      local h1, h2, h3, h4 = H[1], H[2], H[3], H[4]
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = ((d * 256 + c) * 256 + b) * 256 + a
         end
         local a, b, c, d = h1, h2, h3, h4
         local s = 32-7
         for j = 1, 16 do
            local F = ROR(AND(b, c) + AND(-1-b, d) + a + K[j] + W[j], s) + b
            s = md5_next_shift[s]
            a = d
            d = c
            c = b
            b = F
         end
         s = 32-5
         for j = 17, 32 do
            local F = ROR(AND(d, b) + AND(-1-d, c) + a + K[j] + W[(5*j-4) % 16 + 1], s) + b
            s = md5_next_shift[s]
            a = d
            d = c
            c = b
            b = F
         end
         s = 32-4
         for j = 33, 48 do
            local F = ROR(XOR(XOR(b, c), d) + a + K[j] + W[(3*j+2) % 16 + 1], s) + b
            s = md5_next_shift[s]
            a = d
            d = c
            c = b
            b = F
         end
         s = 32-6
         for j = 49, 64 do
            local F = ROR(XOR(c, OR(b, -1-d)) + a + K[j] + W[(j*7-7) % 16 + 1], s) + b
            s = md5_next_shift[s]
            a = d
            d = c
            c = b
            b = F
         end
         h1 = (a + h1) % 4294967296
         h2 = (b + h2) % 4294967296
         h3 = (c + h3) % 4294967296
         h4 = (d + h4) % 4294967296
      end
      H[1], H[2], H[3], H[4] = h1, h2, h3, h4
   end

   function sha1_feed_64(H, str, offs, size)
      -- offs >= 0, size >= 0, size is multiple of 64
      local W = common_W
      local h1, h2, h3, h4, h5 = H[1], H[2], H[3], H[4], H[5]
      for pos = offs, offs + size - 1, 64 do
         for j = 1, 16 do
            pos = pos + 4
            local a, b, c, d = byte(str, pos - 3, pos)
            W[j] = ((a * 256 + b) * 256 + c) * 256 + d
         end
         for j = 17, 80 do
            W[j] = ROL(XOR(W[j-3], W[j-8], W[j-14], W[j-16]), 1)
         end
         local a, b, c, d, e = h1, h2, h3, h4, h5
         for j = 1, 20 do
            local z = ROL(a, 5) + AND(b, c) + AND(-1-b, d) + 0x5A827999 + W[j] + e        -- constant = floor(2^30 * sqrt(2))
            e = d
            d = c
            c = ROR(b, 2)
            b = a
            a = z
         end
         for j = 21, 40 do
            local z = ROL(a, 5) + XOR(b, c, d) + 0x6ED9EBA1 + W[j] + e                    -- 2^30 * sqrt(3)
            e = d
            d = c
            c = ROR(b, 2)
            b = a
            a = z
         end
         for j = 41, 60 do
            local z = ROL(a, 5) + AND(d, c) + AND(b, XOR(d, c)) + 0x8F1BBCDC + W[j] + e   -- 2^30 * sqrt(5)
            e = d
            d = c
            c = ROR(b, 2)
            b = a
            a = z
         end
         for j = 61, 80 do
            local z = ROL(a, 5) + XOR(b, c, d) + 0xCA62C1D6 + W[j] + e                    -- 2^30 * sqrt(10)
            e = d
            d = c
            c = ROR(b, 2)
            b = a
            a = z
         end
         h1 = (a + h1) % 4294967296
         h2 = (b + h2) % 4294967296
         h3 = (c + h3) % 4294967296
         h4 = (d + h4) % 4294967296
         h5 = (e + h5) % 4294967296
      end
      H[1], H[2], H[3], H[4], H[5] = h1, h2, h3, h4, h5
   end

   function keccak_feed(lanes_lo, lanes_hi, str, offs, size, block_size_in_bytes)
      -- This is an example of a Lua function having 79 local variables :-)
      -- offs >= 0, size >= 0, size is multiple of block_size_in_bytes, block_size_in_bytes is positive multiple of 8
      local RC_lo, RC_hi = sha3_RC_lo, sha3_RC_hi
      local qwords_qty = block_size_in_bytes / 8
      for pos = offs, offs + size - 1, block_size_in_bytes do
         for j = 1, qwords_qty do
            local a, b, c, d = byte(str, pos + 1, pos + 4)
            lanes_lo[j] = XOR(lanes_lo[j], ((d * 256 + c) * 256 + b) * 256 + a)
            pos = pos + 8
            a, b, c, d = byte(str, pos - 3, pos)
            lanes_hi[j] = XOR(lanes_hi[j], ((d * 256 + c) * 256 + b) * 256 + a)
         end
         local L01_lo, L01_hi, L02_lo, L02_hi, L03_lo, L03_hi, L04_lo, L04_hi, L05_lo, L05_hi, L06_lo, L06_hi, L07_lo, L07_hi, L08_lo, L08_hi,
            L09_lo, L09_hi, L10_lo, L10_hi, L11_lo, L11_hi, L12_lo, L12_hi, L13_lo, L13_hi, L14_lo, L14_hi, L15_lo, L15_hi, L16_lo, L16_hi,
            L17_lo, L17_hi, L18_lo, L18_hi, L19_lo, L19_hi, L20_lo, L20_hi, L21_lo, L21_hi, L22_lo, L22_hi, L23_lo, L23_hi, L24_lo, L24_hi, L25_lo, L25_hi =
            lanes_lo[1], lanes_hi[1], lanes_lo[2], lanes_hi[2], lanes_lo[3], lanes_hi[3], lanes_lo[4], lanes_hi[4], lanes_lo[5], lanes_hi[5],
            lanes_lo[6], lanes_hi[6], lanes_lo[7], lanes_hi[7], lanes_lo[8], lanes_hi[8], lanes_lo[9], lanes_hi[9], lanes_lo[10], lanes_hi[10],
            lanes_lo[11], lanes_hi[11], lanes_lo[12], lanes_hi[12], lanes_lo[13], lanes_hi[13], lanes_lo[14], lanes_hi[14], lanes_lo[15], lanes_hi[15],
            lanes_lo[16], lanes_hi[16], lanes_lo[17], lanes_hi[17], lanes_lo[18], lanes_hi[18], lanes_lo[19], lanes_hi[19], lanes_lo[20], lanes_hi[20],
            lanes_lo[21], lanes_hi[21], lanes_lo[22], lanes_hi[22], lanes_lo[23], lanes_hi[23], lanes_lo[24], lanes_hi[24], lanes_lo[25], lanes_hi[25]
         for round_idx = 1, 24 do
            local C1_lo = XOR(L01_lo, L06_lo, L11_lo, L16_lo, L21_lo)
            local C1_hi = XOR(L01_hi, L06_hi, L11_hi, L16_hi, L21_hi)
            local C2_lo = XOR(L02_lo, L07_lo, L12_lo, L17_lo, L22_lo)
            local C2_hi = XOR(L02_hi, L07_hi, L12_hi, L17_hi, L22_hi)
            local C3_lo = XOR(L03_lo, L08_lo, L13_lo, L18_lo, L23_lo)
            local C3_hi = XOR(L03_hi, L08_hi, L13_hi, L18_hi, L23_hi)
            local C4_lo = XOR(L04_lo, L09_lo, L14_lo, L19_lo, L24_lo)
            local C4_hi = XOR(L04_hi, L09_hi, L14_hi, L19_hi, L24_hi)
            local C5_lo = XOR(L05_lo, L10_lo, L15_lo, L20_lo, L25_lo)
            local C5_hi = XOR(L05_hi, L10_hi, L15_hi, L20_hi, L25_hi)
            local D_lo = XOR(C1_lo, C3_lo * 2 + (C3_hi % 2^32 - C3_hi % 2^31) / 2^31)
            local D_hi = XOR(C1_hi, C3_hi * 2 + (C3_lo % 2^32 - C3_lo % 2^31) / 2^31)
            local T0_lo = XOR(D_lo, L02_lo)
            local T0_hi = XOR(D_hi, L02_hi)
            local T1_lo = XOR(D_lo, L07_lo)
            local T1_hi = XOR(D_hi, L07_hi)
            local T2_lo = XOR(D_lo, L12_lo)
            local T2_hi = XOR(D_hi, L12_hi)
            local T3_lo = XOR(D_lo, L17_lo)
            local T3_hi = XOR(D_hi, L17_hi)
            local T4_lo = XOR(D_lo, L22_lo)
            local T4_hi = XOR(D_hi, L22_hi)
            L02_lo = (T1_lo % 2^32 - T1_lo % 2^20) / 2^20 + T1_hi * 2^12
            L02_hi = (T1_hi % 2^32 - T1_hi % 2^20) / 2^20 + T1_lo * 2^12
            L07_lo = (T3_lo % 2^32 - T3_lo % 2^19) / 2^19 + T3_hi * 2^13
            L07_hi = (T3_hi % 2^32 - T3_hi % 2^19) / 2^19 + T3_lo * 2^13
            L12_lo = T0_lo * 2 + (T0_hi % 2^32 - T0_hi % 2^31) / 2^31
            L12_hi = T0_hi * 2 + (T0_lo % 2^32 - T0_lo % 2^31) / 2^31
            L17_lo = T2_lo * 2^10 + (T2_hi % 2^32 - T2_hi % 2^22) / 2^22
            L17_hi = T2_hi * 2^10 + (T2_lo % 2^32 - T2_lo % 2^22) / 2^22
            L22_lo = T4_lo * 2^2 + (T4_hi % 2^32 - T4_hi % 2^30) / 2^30
            L22_hi = T4_hi * 2^2 + (T4_lo % 2^32 - T4_lo % 2^30) / 2^30
            D_lo = XOR(C2_lo, C4_lo * 2 + (C4_hi % 2^32 - C4_hi % 2^31) / 2^31)
            D_hi = XOR(C2_hi, C4_hi * 2 + (C4_lo % 2^32 - C4_lo % 2^31) / 2^31)
            T0_lo = XOR(D_lo, L03_lo)
            T0_hi = XOR(D_hi, L03_hi)
            T1_lo = XOR(D_lo, L08_lo)
            T1_hi = XOR(D_hi, L08_hi)
            T2_lo = XOR(D_lo, L13_lo)
            T2_hi = XOR(D_hi, L13_hi)
            T3_lo = XOR(D_lo, L18_lo)
            T3_hi = XOR(D_hi, L18_hi)
            T4_lo = XOR(D_lo, L23_lo)
            T4_hi = XOR(D_hi, L23_hi)
            L03_lo = (T2_lo % 2^32 - T2_lo % 2^21) / 2^21 + T2_hi * 2^11
            L03_hi = (T2_hi % 2^32 - T2_hi % 2^21) / 2^21 + T2_lo * 2^11
            L08_lo = (T4_lo % 2^32 - T4_lo % 2^3) / 2^3 + T4_hi * 2^29 % 2^32
            L08_hi = (T4_hi % 2^32 - T4_hi % 2^3) / 2^3 + T4_lo * 2^29 % 2^32
            L13_lo = T1_lo * 2^6 + (T1_hi % 2^32 - T1_hi % 2^26) / 2^26
            L13_hi = T1_hi * 2^6 + (T1_lo % 2^32 - T1_lo % 2^26) / 2^26
            L18_lo = T3_lo * 2^15 + (T3_hi % 2^32 - T3_hi % 2^17) / 2^17
            L18_hi = T3_hi * 2^15 + (T3_lo % 2^32 - T3_lo % 2^17) / 2^17
            L23_lo = (T0_lo % 2^32 - T0_lo % 2^2) / 2^2 + T0_hi * 2^30 % 2^32
            L23_hi = (T0_hi % 2^32 - T0_hi % 2^2) / 2^2 + T0_lo * 2^30 % 2^32
            D_lo = XOR(C3_lo, C5_lo * 2 + (C5_hi % 2^32 - C5_hi % 2^31) / 2^31)
            D_hi = XOR(C3_hi, C5_hi * 2 + (C5_lo % 2^32 - C5_lo % 2^31) / 2^31)
            T0_lo = XOR(D_lo, L04_lo)
            T0_hi = XOR(D_hi, L04_hi)
            T1_lo = XOR(D_lo, L09_lo)
            T1_hi = XOR(D_hi, L09_hi)
            T2_lo = XOR(D_lo, L14_lo)
            T2_hi = XOR(D_hi, L14_hi)
            T3_lo = XOR(D_lo, L19_lo)
            T3_hi = XOR(D_hi, L19_hi)
            T4_lo = XOR(D_lo, L24_lo)
            T4_hi = XOR(D_hi, L24_hi)
            L04_lo = T3_lo * 2^21 % 2^32 + (T3_hi % 2^32 - T3_hi % 2^11) / 2^11
            L04_hi = T3_hi * 2^21 % 2^32 + (T3_lo % 2^32 - T3_lo % 2^11) / 2^11
            L09_lo = T0_lo * 2^28 % 2^32 + (T0_hi % 2^32 - T0_hi % 2^4) / 2^4
            L09_hi = T0_hi * 2^28 % 2^32 + (T0_lo % 2^32 - T0_lo % 2^4) / 2^4
            L14_lo = T2_lo * 2^25 % 2^32 + (T2_hi % 2^32 - T2_hi % 2^7) / 2^7
            L14_hi = T2_hi * 2^25 % 2^32 + (T2_lo % 2^32 - T2_lo % 2^7) / 2^7
            L19_lo = (T4_lo % 2^32 - T4_lo % 2^8) / 2^8 + T4_hi * 2^24 % 2^32
            L19_hi = (T4_hi % 2^32 - T4_hi % 2^8) / 2^8 + T4_lo * 2^24 % 2^32
            L24_lo = (T1_lo % 2^32 - T1_lo % 2^9) / 2^9 + T1_hi * 2^23 % 2^32
            L24_hi = (T1_hi % 2^32 - T1_hi % 2^9) / 2^9 + T1_lo * 2^23 % 2^32
            D_lo = XOR(C4_lo, C1_lo * 2 + (C1_hi % 2^32 - C1_hi % 2^31) / 2^31)
            D_hi = XOR(C4_hi, C1_hi * 2 + (C1_lo % 2^32 - C1_lo % 2^31) / 2^31)
            T0_lo = XOR(D_lo, L05_lo)
            T0_hi = XOR(D_hi, L05_hi)
            T1_lo = XOR(D_lo, L10_lo)
            T1_hi = XOR(D_hi, L10_hi)
            T2_lo = XOR(D_lo, L15_lo)
            T2_hi = XOR(D_hi, L15_hi)
            T3_lo = XOR(D_lo, L20_lo)
            T3_hi = XOR(D_hi, L20_hi)
            T4_lo = XOR(D_lo, L25_lo)
            T4_hi = XOR(D_hi, L25_hi)
            L05_lo = T4_lo * 2^14 + (T4_hi % 2^32 - T4_hi % 2^18) / 2^18
            L05_hi = T4_hi * 2^14 + (T4_lo % 2^32 - T4_lo % 2^18) / 2^18
            L10_lo = T1_lo * 2^20 % 2^32 + (T1_hi % 2^32 - T1_hi % 2^12) / 2^12
            L10_hi = T1_hi * 2^20 % 2^32 + (T1_lo % 2^32 - T1_lo % 2^12) / 2^12
            L15_lo = T3_lo * 2^8 + (T3_hi % 2^32 - T3_hi % 2^24) / 2^24
            L15_hi = T3_hi * 2^8 + (T3_lo % 2^32 - T3_lo % 2^24) / 2^24
            L20_lo = T0_lo * 2^27 % 2^32 + (T0_hi % 2^32 - T0_hi % 2^5) / 2^5
            L20_hi = T0_hi * 2^27 % 2^32 + (T0_lo % 2^32 - T0_lo % 2^5) / 2^5
            L25_lo = (T2_lo % 2^32 - T2_lo % 2^25) / 2^25 + T2_hi * 2^7
            L25_hi = (T2_hi % 2^32 - T2_hi % 2^25) / 2^25 + T2_lo * 2^7
            D_lo = XOR(C5_lo, C2_lo * 2 + (C2_hi % 2^32 - C2_hi % 2^31) / 2^31)
            D_hi = XOR(C5_hi, C2_hi * 2 + (C2_lo % 2^32 - C2_lo % 2^31) / 2^31)
            T1_lo = XOR(D_lo, L06_lo)
            T1_hi = XOR(D_hi, L06_hi)
            T2_lo = XOR(D_lo, L11_lo)
            T2_hi = XOR(D_hi, L11_hi)
            T3_lo = XOR(D_lo, L16_lo)
            T3_hi = XOR(D_hi, L16_hi)
            T4_lo = XOR(D_lo, L21_lo)
            T4_hi = XOR(D_hi, L21_hi)
            L06_lo = T2_lo * 2^3 + (T2_hi % 2^32 - T2_hi % 2^29) / 2^29
            L06_hi = T2_hi * 2^3 + (T2_lo % 2^32 - T2_lo % 2^29) / 2^29
            L11_lo = T4_lo * 2^18 + (T4_hi % 2^32 - T4_hi % 2^14) / 2^14
            L11_hi = T4_hi * 2^18 + (T4_lo % 2^32 - T4_lo % 2^14) / 2^14
            L16_lo = (T1_lo % 2^32 - T1_lo % 2^28) / 2^28 + T1_hi * 2^4
            L16_hi = (T1_hi % 2^32 - T1_hi % 2^28) / 2^28 + T1_lo * 2^4
            L21_lo = (T3_lo % 2^32 - T3_lo % 2^23) / 2^23 + T3_hi * 2^9
            L21_hi = (T3_hi % 2^32 - T3_hi % 2^23) / 2^23 + T3_lo * 2^9
            L01_lo = XOR(D_lo, L01_lo)
            L01_hi = XOR(D_hi, L01_hi)
            L01_lo, L02_lo, L03_lo, L04_lo, L05_lo = XOR(L01_lo, AND(-1-L02_lo, L03_lo)), XOR(L02_lo, AND(-1-L03_lo, L04_lo)), XOR(L03_lo, AND(-1-L04_lo, L05_lo)), XOR(L04_lo, AND(-1-L05_lo, L01_lo)), XOR(L05_lo, AND(-1-L01_lo, L02_lo))
            L01_hi, L02_hi, L03_hi, L04_hi, L05_hi = XOR(L01_hi, AND(-1-L02_hi, L03_hi)), XOR(L02_hi, AND(-1-L03_hi, L04_hi)), XOR(L03_hi, AND(-1-L04_hi, L05_hi)), XOR(L04_hi, AND(-1-L05_hi, L01_hi)), XOR(L05_hi, AND(-1-L01_hi, L02_hi))
            L06_lo, L07_lo, L08_lo, L09_lo, L10_lo = XOR(L09_lo, AND(-1-L10_lo, L06_lo)), XOR(L10_lo, AND(-1-L06_lo, L07_lo)), XOR(L06_lo, AND(-1-L07_lo, L08_lo)), XOR(L07_lo, AND(-1-L08_lo, L09_lo)), XOR(L08_lo, AND(-1-L09_lo, L10_lo))
            L06_hi, L07_hi, L08_hi, L09_hi, L10_hi = XOR(L09_hi, AND(-1-L10_hi, L06_hi)), XOR(L10_hi, AND(-1-L06_hi, L07_hi)), XOR(L06_hi, AND(-1-L07_hi, L08_hi)), XOR(L07_hi, AND(-1-L08_hi, L09_hi)), XOR(L08_hi, AND(-1-L09_hi, L10_hi))
            L11_lo, L12_lo, L13_lo, L14_lo, L15_lo = XOR(L12_lo, AND(-1-L13_lo, L14_lo)), XOR(L13_lo, AND(-1-L14_lo, L15_lo)), XOR(L14_lo, AND(-1-L15_lo, L11_lo)), XOR(L15_lo, AND(-1-L11_lo, L12_lo)), XOR(L11_lo, AND(-1-L12_lo, L13_lo))
            L11_hi, L12_hi, L13_hi, L14_hi, L15_hi = XOR(L12_hi, AND(-1-L13_hi, L14_hi)), XOR(L13_hi, AND(-1-L14_hi, L15_hi)), XOR(L14_hi, AND(-1-L15_hi, L11_hi)), XOR(L15_hi, AND(-1-L11_hi, L12_hi)), XOR(L11_hi, AND(-1-L12_hi, L13_hi))
            L16_lo, L17_lo, L18_lo, L19_lo, L20_lo = XOR(L20_lo, AND(-1-L16_lo, L17_lo)), XOR(L16_lo, AND(-1-L17_lo, L18_lo)), XOR(L17_lo, AND(-1-L18_lo, L19_lo)), XOR(L18_lo, AND(-1-L19_lo, L20_lo)), XOR(L19_lo, AND(-1-L20_lo, L16_lo))
            L16_hi, L17_hi, L18_hi, L19_hi, L20_hi = XOR(L20_hi, AND(-1-L16_hi, L17_hi)), XOR(L16_hi, AND(-1-L17_hi, L18_hi)), XOR(L17_hi, AND(-1-L18_hi, L19_hi)), XOR(L18_hi, AND(-1-L19_hi, L20_hi)), XOR(L19_hi, AND(-1-L20_hi, L16_hi))
            L21_lo, L22_lo, L23_lo, L24_lo, L25_lo = XOR(L23_lo, AND(-1-L24_lo, L25_lo)), XOR(L24_lo, AND(-1-L25_lo, L21_lo)), XOR(L25_lo, AND(-1-L21_lo, L22_lo)), XOR(L21_lo, AND(-1-L22_lo, L23_lo)), XOR(L22_lo, AND(-1-L23_lo, L24_lo))
            L21_hi, L22_hi, L23_hi, L24_hi, L25_hi = XOR(L23_hi, AND(-1-L24_hi, L25_hi)), XOR(L24_hi, AND(-1-L25_hi, L21_hi)), XOR(L25_hi, AND(-1-L21_hi, L22_hi)), XOR(L21_hi, AND(-1-L22_hi, L23_hi)), XOR(L22_hi, AND(-1-L23_hi, L24_hi))
            L01_lo = XOR(L01_lo, RC_lo[round_idx])
            L01_hi = L01_hi + RC_hi[round_idx]      -- RC_hi[] is either 0 or 0x80000000, so we could use fast addition instead of slow XOR
         end
         lanes_lo[1]  = L01_lo
         lanes_hi[1]  = L01_hi
         lanes_lo[2]  = L02_lo
         lanes_hi[2]  = L02_hi
         lanes_lo[3]  = L03_lo
         lanes_hi[3]  = L03_hi
         lanes_lo[4]  = L04_lo
         lanes_hi[4]  = L04_hi
         lanes_lo[5]  = L05_lo
         lanes_hi[5]  = L05_hi
         lanes_lo[6]  = L06_lo
         lanes_hi[6]  = L06_hi
         lanes_lo[7]  = L07_lo
         lanes_hi[7]  = L07_hi
         lanes_lo[8]  = L08_lo
         lanes_hi[8]  = L08_hi
         lanes_lo[9]  = L09_lo
         lanes_hi[9]  = L09_hi
         lanes_lo[10] = L10_lo
         lanes_hi[10] = L10_hi
         lanes_lo[11] = L11_lo
         lanes_hi[11] = L11_hi
         lanes_lo[12] = L12_lo
         lanes_hi[12] = L12_hi
         lanes_lo[13] = L13_lo
         lanes_hi[13] = L13_hi
         lanes_lo[14] = L14_lo
         lanes_hi[14] = L14_hi
         lanes_lo[15] = L15_lo
         lanes_hi[15] = L15_hi
         lanes_lo[16] = L16_lo
         lanes_hi[16] = L16_hi
         lanes_lo[17] = L17_lo
         lanes_hi[17] = L17_hi
         lanes_lo[18] = L18_lo
         lanes_hi[18] = L18_hi
         lanes_lo[19] = L19_lo
         lanes_hi[19] = L19_hi
         lanes_lo[20] = L20_lo
         lanes_hi[20] = L20_hi
         lanes_lo[21] = L21_lo
         lanes_hi[21] = L21_hi
         lanes_lo[22] = L22_lo
         lanes_hi[22] = L22_hi
         lanes_lo[23] = L23_lo
         lanes_hi[23] = L23_hi
         lanes_lo[24] = L24_lo
         lanes_hi[24] = L24_hi
         lanes_lo[25] = L25_lo
         lanes_hi[25] = L25_hi
      end
   end

end


--------------------------------------------------------------------------------
-- MAGIC NUMBERS CALCULATOR
--------------------------------------------------------------------------------
-- Q:
--    Is 53-bit "double" math enough to calculate square roots and cube roots of primes with 64 correct bits after decimal point?
-- A:
--    Yes, 53-bit "double" arithmetic is enough.
--    We could obtain first 40 bits by direct calculation of p^(1/3) and next 40 bits by one step of Newton's method.

do
   local function mul(src1, src2, factor, result_length)
      -- src1, src2 - long integers (arrays of digits in base 2^24)
      -- factor - small integer
      -- returns long integer result (src1 * src2 * factor) and its floating point approximation
      local result, carry, value, weight = {}, 0.0, 0.0, 1.0
      for j = 1, result_length do
         for k = math_max(1, j + 1 - #src2), math_min(j, #src1) do
            carry = carry + factor * src1[k] * src2[j + 1 - k]  -- "int32" is not enough for multiplication result, that's why "factor" must be of type "double"
         end
         local digit = carry % 2^24
         result[j] = floor(digit)
         carry = (carry - digit) / 2^24
         value = value + digit * weight
         weight = weight * 2^24
      end
      return result, value
   end

   local idx, step, p, one, sqrt_hi, sqrt_lo = 0, {4, 1, 2, -2, 2}, 4, {1}, sha2_H_hi, sha2_H_lo
   repeat
      p = p + step[p % 6]
      local d = 1
      repeat
         d = d + step[d % 6]
         if d*d > p then -- next prime number is found
            local root = p^(1/3)
            local R = root * 2^40
            R = mul({R - R % 1}, one, 1.0, 2)
            local _, delta = mul(R, mul(R, R, 1.0, 4), -1.0, 4)
            local hi = R[2] % 65536 * 65536 + floor(R[1] / 256)
            local lo = R[1] % 256 * 16777216 + floor(delta * (2^-56 / 3) * root / p)
            if idx < 16 then
               root = p^(1/2)
               R = root * 2^40
               R = mul({R - R % 1}, one, 1.0, 2)
               _, delta = mul(R, R, -1.0, 2)
               local hi = R[2] % 65536 * 65536 + floor(R[1] / 256)
               local lo = R[1] % 256 * 16777216 + floor(delta * 2^-17 / root)
               local idx = idx % 8 + 1
               sha2_H_ext256[224][idx] = lo
               sqrt_hi[idx], sqrt_lo[idx] = hi, lo + hi * hi_factor
               if idx > 7 then
                  sqrt_hi, sqrt_lo = sha2_H_ext512_hi[384], sha2_H_ext512_lo[384]
               end
            end
            idx = idx + 1
            sha2_K_hi[idx], sha2_K_lo[idx] = hi, lo % K_lo_modulo + hi * hi_factor
            break
         end
      until p % d == 0
   until idx > 79
end

-- Calculating IVs for SHA512/224 and SHA512/256
for width = 224, 256, 32 do
   local H_lo, H_hi = {}
   if XOR64A5 then
      for j = 1, 8 do
         H_lo[j] = XOR64A5(sha2_H_lo[j])
      end
   else
      H_hi = {}
      for j = 1, 8 do
         H_lo[j] = XOR32A5(sha2_H_lo[j])
         H_hi[j] = XOR32A5(sha2_H_hi[j])
      end
   end
   sha512_feed_128(H_lo, H_hi, "SHA-512/"..tostring(width).."\128"..string_rep("\0", 115).."\88", 0, 128)
   sha2_H_ext512_lo[width] = H_lo
   sha2_H_ext512_hi[width] = H_hi
end

-- Constants for MD5
do
   local sin, abs, modf = math.sin, math.abs, math.modf
   for idx = 1, 64 do
      -- we can't use formula floor(abs(sin(idx))*2^32) because its result may be beyond integer range on Lua built with 32-bit integers
      local hi, lo = modf(abs(sin(idx)) * 2^16)
      md5_K[idx] = hi * 65536 + floor(lo * 2^16)
   end
end

-- Constants for SHA3
do
   local sh_reg = 29
   local function next_bit()
      local r = sh_reg % 2
      sh_reg = XOR_BYTE((sh_reg - r) / 2, 142 * r)
      return r
   end
   for idx = 1, 24 do
      local lo, m = 0
      for _ = 1, 6 do
         m = m and m * m * 2 or 1
         lo = lo + next_bit() * m
      end
      local hi = next_bit() * m
      sha3_RC_hi[idx], sha3_RC_lo[idx] = hi, lo + hi * hi_factor_keccak
   end
end


--------------------------------------------------------------------------------
-- MAIN FUNCTIONS
--------------------------------------------------------------------------------

local function sha256ext(width, message)

   -- Create an instance (private objects for current calculation)
   local H, length, tail = {unpack(sha2_H_ext256[width])}, 0.0, ""

   local function partial(message_part)
      if message_part then
         if tail then
            length = length + #message_part
            local offs = 0
            if tail ~= "" and #tail + #message_part >= 64 then
               offs = 64 - #tail
               sha256_feed_64(H, tail..sub(message_part, 1, offs), 0, 64)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size % 64
            sha256_feed_64(H, message_part, offs, size - size_tail)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            local final_blocks = {tail, "\128", string_rep("\0", (-9 - length) % 64 + 1)}
            tail = nil
            -- Assuming user data length is shorter than (2^53)-9 bytes
            -- Anyway, it looks very unrealistic that someone would spend more than a year of calculations to process 2^53 bytes of data by using this Lua script :-)
            -- 2^53 bytes = 2^56 bits, so "bit-counter" fits in 7 bytes
            length = length * (8 / 256^7)  -- convert "byte-counter" to "bit-counter" and move decimal point to the left
            for j = 4, 10 do
               length = length % 1 * 256
               final_blocks[j] = char(floor(length))
            end
            final_blocks = table_concat(final_blocks)
            sha256_feed_64(H, final_blocks, 0, #final_blocks)
            local max_reg = width / 32
            for j = 1, max_reg do
               H[j] = HEX(H[j])
            end
            H = table_concat(H, "", 1, max_reg)
         end
         return H
      end
   end

   if message then
      -- Actually perform calculations and return the SHA256 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get SHA256 digest by invoking this function without an argument
      return partial
   end

end


local function sha512ext(width, message)

   -- Create an instance (private objects for current calculation)
   local length, tail, H_lo, H_hi = 0.0, "", {unpack(sha2_H_ext512_lo[width])}, not HEX64 and {unpack(sha2_H_ext512_hi[width])}

   local function partial(message_part)
      if message_part then
         if tail then
            length = length + #message_part
            local offs = 0
            if tail ~= "" and #tail + #message_part >= 128 then
               offs = 128 - #tail
               sha512_feed_128(H_lo, H_hi, tail..sub(message_part, 1, offs), 0, 128)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size % 128
            sha512_feed_128(H_lo, H_hi, message_part, offs, size - size_tail)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            local final_blocks = {tail, "\128", string_rep("\0", (-17-length) % 128 + 9)}
            tail = nil
            -- Assuming user data length is shorter than (2^53)-17 bytes
            -- 2^53 bytes = 2^56 bits, so "bit-counter" fits in 7 bytes
            length = length * (8 / 256^7)  -- convert "byte-counter" to "bit-counter" and move floating point to the left
            for j = 4, 10 do
               length = length % 1 * 256
               final_blocks[j] = char(floor(length))
            end
            final_blocks = table_concat(final_blocks)
            sha512_feed_128(H_lo, H_hi, final_blocks, 0, #final_blocks)
            local max_reg = ceil(width / 64)
            if HEX64 then
               for j = 1, max_reg do
                  H_lo[j] = HEX64(H_lo[j])
               end
            else
               for j = 1, max_reg do
                  H_lo[j] = HEX(H_hi[j])..HEX(H_lo[j])
               end
               H_hi = nil
            end
            H_lo = sub(table_concat(H_lo, "", 1, max_reg), 1, width / 4)
         end
         return H_lo
      end
   end

   if message then
      -- Actually perform calculations and return the SHA512 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get SHA512 digest by invoking this function without an argument
      return partial
   end

end


local function md5(message)

   -- Create an instance (private objects for current calculation)
   local H, length, tail = {unpack(md5_sha1_H, 1, 4)}, 0.0, ""

   local function partial(message_part)
      if message_part then
         if tail then
            length = length + #message_part
            local offs = 0
            if tail ~= "" and #tail + #message_part >= 64 then
               offs = 64 - #tail
               md5_feed_64(H, tail..sub(message_part, 1, offs), 0, 64)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size % 64
            md5_feed_64(H, message_part, offs, size - size_tail)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            local final_blocks = {tail, "\128", string_rep("\0", (-9 - length) % 64)}
            tail = nil
            length = length * 8  -- convert "byte-counter" to "bit-counter"
            for j = 4, 11 do
               local low_byte = length % 256
               final_blocks[j] = char(low_byte)
               length = (length - low_byte) / 256
            end
            final_blocks = table_concat(final_blocks)
            md5_feed_64(H, final_blocks, 0, #final_blocks)
            for j = 1, 4 do
               H[j] = HEX(H[j])
            end
            H = gsub(table_concat(H), "(..)(..)(..)(..)", "%4%3%2%1")
         end
         return H
      end
   end

   if message then
      -- Actually perform calculations and return the MD5 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get MD5 digest by invoking this function without an argument
      return partial
   end

end


local function sha1(message)

   -- Create an instance (private objects for current calculation)
   local H, length, tail = {unpack(md5_sha1_H)}, 0.0, ""

   local function partial(message_part)
      if message_part then
         if tail then
            length = length + #message_part
            local offs = 0
            if tail ~= "" and #tail + #message_part >= 64 then
               offs = 64 - #tail
               sha1_feed_64(H, tail..sub(message_part, 1, offs), 0, 64)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size % 64
            sha1_feed_64(H, message_part, offs, size - size_tail)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            local final_blocks = {tail, "\128", string_rep("\0", (-9 - length) % 64 + 1)}
            tail = nil
            -- Assuming user data length is shorter than (2^53)-9 bytes
            -- 2^53 bytes = 2^56 bits, so "bit-counter" fits in 7 bytes
            length = length * (8 / 256^7)  -- convert "byte-counter" to "bit-counter" and move decimal point to the left
            for j = 4, 10 do
               length = length % 1 * 256
               final_blocks[j] = char(floor(length))
            end
            final_blocks = table_concat(final_blocks)
            sha1_feed_64(H, final_blocks, 0, #final_blocks)
            for j = 1, 5 do
               H[j] = HEX(H[j])
            end
            H = table_concat(H)
         end
         return H
      end
   end

   if message then
      -- Actually perform calculations and return the SHA-1 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get SHA-1 digest by invoking this function without an argument
      return partial
   end

end


local function keccak(block_size_in_bytes, digest_size_in_bytes, is_SHAKE, message)
   -- "block_size_in_bytes" is multiple of 8
   if type(digest_size_in_bytes) ~= "number" then
      -- arguments in SHAKE are swapped:
      --    NIST FIPS 202 defines SHAKE(message,num_bits)
      --    this module   defines SHAKE(num_bytes,message)
      -- it's easy to forget about this swap, hence the check
      error("Argument 'digest_size_in_bytes' must be a number", 2)
   end

   -- Create an instance (private objects for current calculation)
   local tail, lanes_lo, lanes_hi = "", create_array_of_lanes(), hi_factor_keccak == 0 and create_array_of_lanes()
   local result

--~     pad the input N using the pad function, yielding a padded bit string P with a length divisible by r (such that n = len(P)/r is integer),
--~     break P into n consecutive r-bit pieces P0, ..., Pn-1 (last is zero-padded)
--~     initialize the state S to a string of b 0 bits.
--~     absorb the input into the state: For each block Pi,
--~         extend Pi at the end by a string of c 0 bits, yielding one of length b,
--~         XOR that with S and
--~         apply the block permutation f to the result, yielding a new state S
--~     initialize Z to be the empty string
--~     while the length of Z is less than d:
--~         append the first r bits of S to Z
--~         if Z is still less than d bits long, apply f to S, yielding a new state S.
--~     truncate Z to d bits

   local function partial(message_part)
      if message_part then
         if tail then
            local offs = 0
            if tail ~= "" and #tail + #message_part >= block_size_in_bytes then
               offs = block_size_in_bytes - #tail
               keccak_feed(lanes_lo, lanes_hi, tail..sub(message_part, 1, offs), 0, block_size_in_bytes, block_size_in_bytes)
               tail = ""
            end
            local size = #message_part - offs
            local size_tail = size % block_size_in_bytes
            keccak_feed(lanes_lo, lanes_hi, message_part, offs, size - size_tail, block_size_in_bytes)
            tail = tail..sub(message_part, #message_part + 1 - size_tail)
            return partial
         else
            error("Adding more chunks is not allowed after receiving the result", 2)
         end
      else
         if tail then
            -- append the following bits to the message: for usual SHA3: 011(0*)1, for SHAKE: 11111(0*)1
            local gap_start = is_SHAKE and 31 or 6
            tail = tail..(#tail + 1 == block_size_in_bytes and char(gap_start + 128) or char(gap_start)..string_rep("\0", (-2 - #tail) % block_size_in_bytes).."\128")
            keccak_feed(lanes_lo, lanes_hi, tail, 0, #tail, block_size_in_bytes)
            tail = nil

            local lanes_used = 0
            local total_lanes = floor(block_size_in_bytes / 8)
            local qwords = {}

            local function get_next_qwords_of_digest(qwords_qty)
               -- returns not more than 'qwords_qty' qwords ('qwords_qty' might be non-integer)
               -- doesn't go across keccak-buffer boundary
               -- block_size_in_bytes is a multiple of 8, so, keccak-buffer contains integer number of qwords
               if lanes_used >= total_lanes then
                  keccak_feed(lanes_lo, lanes_hi, "\0\0\0\0\0\0\0\0", 0, 8, 8)
                  lanes_used = 0
               end
               qwords_qty = floor(math_min(qwords_qty, total_lanes - lanes_used))
               if hi_factor_keccak ~= 0 then
                  for j = 1, qwords_qty do
                     qwords[j] = HEX64(lanes_lo[lanes_used + j - 1 + lanes_index_base])
                  end
               else
                  for j = 1, qwords_qty do
                     qwords[j] = HEX(lanes_hi[lanes_used + j])..HEX(lanes_lo[lanes_used + j])
                  end
               end
               lanes_used = lanes_used + qwords_qty
               return
                  gsub(table_concat(qwords, "", 1, qwords_qty), "(..)(..)(..)(..)(..)(..)(..)(..)", "%8%7%6%5%4%3%2%1"),
                  qwords_qty * 8
            end

            local parts = {}      -- digest parts
            local last_part, last_part_size = "", 0

            local function get_next_part_of_digest(bytes_needed)
               -- returns 'bytes_needed' bytes, for arbitrary integer 'bytes_needed'
               bytes_needed = bytes_needed or 1
               if bytes_needed <= last_part_size then
                  last_part_size = last_part_size - bytes_needed
                  local part_size_in_nibbles = bytes_needed * 2
                  local result = sub(last_part, 1, part_size_in_nibbles)
                  last_part = sub(last_part, part_size_in_nibbles + 1)
                  return result
               end
               local parts_qty = 0
               if last_part_size > 0 then
                  parts_qty = 1
                  parts[parts_qty] = last_part
                  bytes_needed = bytes_needed - last_part_size
               end
               -- repeats until the length is enough
               while bytes_needed >= 8 do
                  local next_part, next_part_size = get_next_qwords_of_digest(bytes_needed / 8)
                  parts_qty = parts_qty + 1
                  parts[parts_qty] = next_part
                  bytes_needed = bytes_needed - next_part_size
               end
               if bytes_needed > 0 then
                  last_part, last_part_size = get_next_qwords_of_digest(1)
                  parts_qty = parts_qty + 1
                  parts[parts_qty] = get_next_part_of_digest(bytes_needed)
               else
                  last_part, last_part_size = "", 0
               end
               return table_concat(parts, "", 1, parts_qty)
            end

            if digest_size_in_bytes < 0 then
               result = get_next_part_of_digest
            else
               result = get_next_part_of_digest(digest_size_in_bytes)
            end

         end
         return result
      end
   end

   if message then
      -- Actually perform calculations and return the SHA3 digest of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading
      -- User should feed every chunk of input data as single argument to this function and finally get SHA3 digest by invoking this function without an argument
      return partial
   end

end


local hex2bin, bin2base64, base642bin
do

   function hex2bin(hex_string)
      return (gsub(hex_string, "%x%x",
         function (hh)
            return char(tonumber(hh, 16))
         end
      ))
   end

   local base64_symbols = {
      ['+'] = 62, ['-'] = 62,  [62] = '+',
      ['/'] = 63, ['_'] = 63,  [63] = '/',
      ['='] = -1, ['.'] = -1,  [-1] = '='
   }
   local symbol_index = 0
   for j, pair in ipairs{'AZ', 'az', '09'} do
      for ascii = byte(pair), byte(pair, 2) do
         local ch = char(ascii)
         base64_symbols[ch] = symbol_index
         base64_symbols[symbol_index] = ch
         symbol_index = symbol_index + 1
      end
   end

   function bin2base64(binary_string)
      local result = {}
      for pos = 1, #binary_string, 3 do
         local c1, c2, c3, c4 = byte(sub(binary_string, pos, pos + 2)..'\0', 1, -1)
         result[#result + 1] =
            base64_symbols[floor(c1 / 4)]
            ..base64_symbols[c1 % 4 * 16 + floor(c2 / 16)]
            ..base64_symbols[c3 and c2 % 16 * 4 + floor(c3 / 64) or -1]
            ..base64_symbols[c4 and c3 % 64 or -1]
      end
      return table_concat(result)
   end

   function base642bin(base64_string)
      local result, chars_qty = {}, 3
      for pos, ch in gmatch(gsub(base64_string, '%s+', ''), '()(.)') do
         local code = base64_symbols[ch]
         if code < 0 then
            chars_qty = chars_qty - 1
            code = 0
         end
         local idx = pos % 4
         if idx > 0 then
            result[-idx] = code
         else
            local c1 = result[-1] * 4 + floor(result[-2] / 16)
            local c2 = (result[-2] % 16) * 16 + floor(result[-3] / 4)
            local c3 = (result[-3] % 4) * 64 + code
            result[#result + 1] = sub(char(c1, c2, c3), 1, chars_qty)
         end
      end
      return table_concat(result)
   end

end


local block_size_for_HMAC  -- this table will be initialized at the end of the module

local function pad_and_xor(str, result_length, byte_for_xor)
   return gsub(str, ".",
      function(c)
         return char(XOR_BYTE(byte(c), byte_for_xor))
      end
   )..string_rep(char(byte_for_xor), result_length - #str)
end

local function hmac(hash_func, key, message)

   -- Create an instance (private objects for current calculation)
   local block_size = block_size_for_HMAC[hash_func]
   if not block_size then
      error("Unknown hash function", 2)
   end
   if #key > block_size then
      key = hex2bin(hash_func(key))
   end
   local append = hash_func()(pad_and_xor(key, block_size, 0x36))
   local result

   local function partial(message_part)
      if not message_part then
         result = result or hash_func(pad_and_xor(key, block_size, 0x5C)..hex2bin(append()))
         return result
      elseif result then
         error("Adding more chunks is not allowed after receiving the result", 2)
      else
         append(message_part)
         return partial
      end
   end

   if message then
      -- Actually perform calculations and return the HMAC of a message
      return partial(message)()
   else
      -- Return function for chunk-by-chunk loading of a message
      -- User should feed every chunk of the message as single argument to this function and finally get HMAC by invoking this function without an argument
      return partial
   end

end


local sha = {
   md5        = md5,                                                                                                                   -- MD5
   sha1       = sha1,                                                                                                                  -- SHA-1
   -- SHA2 hash functions:
   sha224     = function (message)                       return sha256ext(224, message)                                           end, -- SHA-224
   sha256     = function (message)                       return sha256ext(256, message)                                           end, -- SHA-256
   sha512_224 = function (message)                       return sha512ext(224, message)                                           end, -- SHA-512/224
   sha512_256 = function (message)                       return sha512ext(256, message)                                           end, -- SHA-512/256
   sha384     = function (message)                       return sha512ext(384, message)                                           end, -- SHA-384
   sha512     = function (message)                       return sha512ext(512, message)                                           end, -- SHA-512
   -- SHA3 hash functions:
   sha3_224   = function (message)                       return keccak((1600 - 2 * 224) / 8, 224 / 8, false, message)             end, -- SHA3-224
   sha3_256   = function (message)                       return keccak((1600 - 2 * 256) / 8, 256 / 8, false, message)             end, -- SHA3-256
   sha3_384   = function (message)                       return keccak((1600 - 2 * 384) / 8, 384 / 8, false, message)             end, -- SHA3-384
   sha3_512   = function (message)                       return keccak((1600 - 2 * 512) / 8, 512 / 8, false, message)             end, -- SHA3-512
   shake128   = function (digest_size_in_bytes, message) return keccak((1600 - 2 * 128) / 8, digest_size_in_bytes, true, message) end, -- SHAKE128
   shake256   = function (digest_size_in_bytes, message) return keccak((1600 - 2 * 256) / 8, digest_size_in_bytes, true, message) end, -- SHAKE256
   -- misc utilities:
   hmac       = hmac,       -- HMAC(hash_func, key, message) is applicable to any hash function from this module except SHAKE*
   hex2bin    = hex2bin,    -- converts hexadecimal representation to binary string
   base642bin = base642bin, -- converts base64 representation to binary string
   bin2base64 = bin2base64, -- converts binary string to base64 representation
}


block_size_for_HMAC = {
   [sha.md5]        = 64,
   [sha.sha1]       = 64,
   [sha.sha224]     = 64,
   [sha.sha256]     = 64,
   [sha.sha512_224] = 128,
   [sha.sha512_256] = 128,
   [sha.sha384]     = 128,
   [sha.sha512]     = 128,
   [sha.sha3_224]   = (1600 - 2 * 224) / 8,
   [sha.sha3_256]   = (1600 - 2 * 256) / 8,
   [sha.sha3_384]   = (1600 - 2 * 384) / 8,
   [sha.sha3_512]   = (1600 - 2 * 512) / 8,
}


return sha