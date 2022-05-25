if fs.isUnlocked then
  local args = {...}
  if args[1] == "lock" or (args[1] == nil and fs.isUnlocked()) then
      fs.lock()
      print("The filesystem is now locked.")
  elseif args[1] == "unlock" or args[1] == nil then
      fs.unlock()
      print("The filesystem is now unlocked.")
  elseif args[1] == "encrypt" then
      if args[3] == nil then error("Usage: fsencrypt encrypt <infile> <outfile>") end
      fs.encrypt(args[2], args[3])
      print(args[2] .. " has been encrypted as " .. args[3] .. ".")
  elseif args[1] == "decrypt" then
      if args[3] == nil then error("Usage: fsencrypt decrypt <infile> <outfile>") end
      fs.decrypt(args[2], args[3])
      print(args[2] .. " has been decrypted as " .. args[3] .. ".")
  elseif args[1] == "help" then
      print([[
Usage:
fsencrypt
  Toggles lock status.
fsencrypt lock
  Locks access to encrypted files.
fsencrypt unlock
  Unlocks access to encrypted files.
fsencrypt encrypt <infile> <outfile>
  Encrypts a file.
fsencrypt decrypt <infile> <outfile>
  Decrypts a file.
fsencrypt help
  Displays this help.]])
  end
  return
end

local aeslua = require "aeslua"
local sha2 = require "sha2"
local expect = require("cc.expect").expect
local sha256 = sha2.sha256

local function sxor(s1, s2)
  local b1 = {}
  local b2 = {}
  local b3 = {}

  for i=1,#s1 do
      b1[#b1+1] = string.byte(s1, i)
  end
  for i=1,#s2 do
      b2[#b2+1] = string.byte(s2, i)
  end
  for i=1,#b1 do
      b3[#b3+1] = string.char(bit32.bxor(b1[i], b2[i]))
  end

  return table.concat(b3)
end

local function hex2bin(str) return str:gsub("%x%x", function(s) return string.char(tonumber(s, 16)) end) end

local function pbkdf2(hm, pass, salt, it)
  local u
  local t

  u = hex2bin(sha2.hmac(hm, pass, salt.."\1"))
  t = u
  for i=2,it do
      u = hex2bin(sha2.hmac(hm, pass, u))
      t = sxor(t, u)
  end

  return t
end

local function iv2bin(iv)
  local retval = ""
  for _,v in ipairs(iv) do retval = retval .. string.char(v) end
  return retval
end

local key, salt, filetree

local orig_fs = fs
_G.fs = {getName = orig_fs.getName, getDrive = orig_fs.getDrive, getFreeSpace = orig_fs.getFreeSpace, combine = orig_fs.combine, getDir = orig_fs.getDir, isDriveRoot = orig_fs.isDriveRoot, getCapacity = orig_fs.getCapacity}

function fs.unlock(password)
  math.randomseed(os.epoch("utc"))
  if not password then
      write("Please enter the password: ")
      password = read("\7")
  end
  local iv
  salt = ""
  if orig_fs.exists("f1a36aae5f891a6c695d12621d1e0ecc4cee1a5e951784d874b8e6ad94de223f") then
      local file = orig_fs.open("f1a36aae5f891a6c695d12621d1e0ecc4cee1a5e951784d874b8e6ad94de223f", "rb")
      local t = file.readAll()
      file.close()
      salt, iv = t:sub(1, 16), {t:sub(17):byte(1, 16)}
  else
      for _ = 1, 16 do salt = salt .. string.char(math.random(0, 255)) end
  end
  key = pbkdf2(sha256, password, salt, 2500)
  password = nil
  filetree = {}
  if orig_fs.exists("9f721fc36d10270affc7dbba9594e7665f95e0ad6d1729f5d9c0e6cc18235cf3") then
      local file = orig_fs.open("9f721fc36d10270affc7dbba9594e7665f95e0ad6d1729f5d9c0e6cc18235cf3", "rb")
      local str = aeslua.decrypt(key, file.readAll(), 32, aeslua.CBCMODE, iv, true)
      file.close()
      if str == nil then
          key, salt, filetree = nil
          error("Incorrect password.", 2)
      end
      filetree = textutils.unserialize(str)
  end
end

local function saveFileTree()
  if key == nil or filetree == nil then return end
  local iv = {}
  if orig_fs.exists("f1a36aae5f891a6c695d12621d1e0ecc4cee1a5e951784d874b8e6ad94de223f") then
      local file = orig_fs.open("f1a36aae5f891a6c695d12621d1e0ecc4cee1a5e951784d874b8e6ad94de223f", "rb")
      local t = file.readAll()
      file.close()
      iv = {t:sub(17):byte(1, 16)}
  else
      for i = 1, 16 do iv[i] = math.random(0, 255) end
      local file = orig_fs.open("f1a36aae5f891a6c695d12621d1e0ecc4cee1a5e951784d874b8e6ad94de223f", "wb")
      file.write(salt .. iv2bin(iv))
      file.close()
  end
  local file = orig_fs.open("9f721fc36d10270affc7dbba9594e7665f95e0ad6d1729f5d9c0e6cc18235cf3", "wb")
  file.write(aeslua.encrypt(key, textutils.serialize(filetree), 32, aeslua.CBCMODE, iv, true))
  file.close()
end

function fs.isUnlocked()
  return key ~= nil and salt ~= nil and filetree ~= nil
end

function fs.lock()
  saveFileTree()
  key, salt, filetree = nil
end

local function splitPath(p)
  local retval = {}
  for m in p:gmatch("[^/]+") do table.insert(retval, m) end
  return retval
end

local function getFileTree(list, t)
  if #list == 0 then return t
  elseif type(t) ~= "table" then return nil
  else
      local i = table.remove(list, 1)
      return getFileTree(list, t[i])
  end
end

local function getFilePath(path) return getFileTree(splitPath(path), filetree) end

local function setFileTree(list, v, t)
  if #list > 1 and t[list[1]] == nil then t[list[1]] = {} end
  if #list == 0 then error("Critical error while writing encrypted data")
  elseif #list == 1 then t[list[1]] = v
  else return setFileTree(list, v, t[table.remove(list, 1)]) end
end

local function setFilePath(path, v) return setFileTree(splitPath(path), v, filetree) end

local shamatch = "^%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x%x$"

local function isSHA(path) return fs.combine(path, ""):match(shamatch) ~= nil or fs.combine(path, "") == ".salt" or fs.combine(path, "") == ".filetree" end

function fs.list(dir)
  expect(1, dir, "string")
  local ok, retval = pcall(orig_fs.list, dir)
  local tree = getFilePath(dir)
  if not ok and type(tree) ~= "table" then error(retval:gsub("^.-:%d: ", ""), 2) end
  retval = ok and retval or {}
  if type(tree) == "table" then for k in pairs(tree) do table.insert(retval, k) end end
  if fs.combine(dir, "") == "" then
      local keep = {}
      for _,v in ipairs(retval) do if not isSHA(v) then table.insert(keep, v) end end
      retval = keep
  end
  table.sort(retval)
  return retval
end

function fs.exists(path)
  expect(1, path, "string")
  if isSHA(path) then return false else return orig_fs.exists(path) or getFilePath(path) ~= nil end
end

function fs.isDir(path)
  expect(1, path, "string")
  if isSHA(path) then return false else return orig_fs.isDir(path) or type(getFilePath(path)) == "table" end
end

function fs.isReadOnly(path)
  expect(1, path, "string")
  return orig_fs.isReadOnly(path) -- more necessary?
end

function fs.getSize(path)
  expect(1, path, "string")
  if isSHA(path) then error("/" .. fs.combine(path, "") .. ": No such file", 2) end
  local ok, retval = pcall(orig_fs.getSize, path)
  local tree = getFilePath(path)
  if not ok and tree == nil then error(retval:gsub("^.-:%d: ", ""), 2)
  elseif type(tree) == "table" then return 0
  elseif ok then return retval end
  local file = fs.open(path, "rb")
  retval = #file.readAll()
  file.close()
  return retval
end

function fs.makeDir(path)
  expect(1, path, "string")
  if isSHA(path) then error("/" .. fs.combine(path, "") .. ": File exists", 2)
  elseif filetree == nil then return orig_fs.makeDir(path)
  elseif type(getFilePath(path)) == "string" then error("/" .. fs.combine(path, "") .. ": File exists", 2) end
  setFilePath(path, getFilePath(path) or {})
  saveFileTree()
end

function fs.move(from, to)
  expect(1, from, "string")
  expect(2, to, "string")
  if isSHA(from) then error("/" .. fs.combine(from, "") .. ": No such file or directory", 2)
  elseif isSHA(to) then error("/" .. fs.combine(to, "") .. ": Permission denied", 2)
  elseif orig_fs.exists(from) or filetree == nil then return orig_fs.move(from, to)
  elseif getFilePath(from) == nil then error("/" .. fs.combine(from, "") .. ": No such file or directory", 2)
  elseif getFilePath(to) ~= nil then error("/" .. fs.combine(to, "") .. ": File exists", 2) end
  setFilePath(to, getFilePath(from))
  setFilePath(from, nil)
  saveFileTree()
end

function fs.copy(from, to)
  expect(1, from, "string")
  expect(2, to, "string")
  if isSHA(from) then error("/" .. fs.combine(from, "") .. ": No such file or directory", 2)
  elseif isSHA(to) then error("/" .. fs.combine(to, "") .. ": Permission denied", 2)
  elseif orig_fs.exists(from) or filetree == nil then return orig_fs.copy(from, to)
  elseif getFilePath(from) == nil then error("/" .. fs.combine(from, "") .. ": No such file or directory", 2)
  elseif getFilePath(to) ~= nil then error("/" .. fs.combine(to, "") .. ": File exists", 2) end
  setFilePath(to, getFilePath(from))
  saveFileTree()
end

function fs.delete(path)
  expect(1, path, "string")
  if isSHA(path) then error("/" .. fs.combine(path, "") .. ": Permission denied", 2)
  elseif orig_fs.exists(path) or filetree == nil then return orig_fs.delete(path) end
  setFilePath(path, nil)
  saveFileTree()
end

function fs.open(path, mode)
  expect(1, path, "string")
  expect(2, mode, "string")
  if isSHA(path) then return nil, ("/" .. fs.combine(path, "") .. (mode:sub(1, 1) ~= "w" and ": No such file" or ": Permission denied"))
  elseif orig_fs.exists(path) or filetree == nil then return orig_fs.open(path, mode)
  elseif ({r=1, w=1, a=1, rb=1, wb=1, ab=1})[mode] == nil then return nil, ("/" .. fs.combine(path, "") .. ": Unknown mode") end
  local contents, pos = "", 1
  local isBinary = mode:sub(2, 2) == "b"
  local closed = false
  if mode:sub(1, 1) ~= "w" then
      local iv = getFilePath(path)
      if type(iv) ~= "string" then return nil, ("/" .. fs.combine(path, "") .. (iv == nil and ": No such file" or ": Is a directory")) end
      local file, err = orig_fs.open(sha256(fs.combine(path, "") .. iv), "rb")
      if not file then return file, err end
      contents = aeslua.decrypt(key, file.readAll(), 32, aeslua.CBCMODE, {iv:byte(1, 16)}, true)
      file.close()
      if contents == nil then return nil, "Failed to decrypt file" end
      if not isBinary then
          local str = ""
          for _,v in utf8.codes(contents) do if v < 256 then str = str .. string.char(v) else str = str .. "?" end end
          contents = str
      end
  end
  if mode:sub(1, 1) == "a" then pos = #contents + 1 end
  if mode:sub(1, 1) == "r" then return {
      read = function(n)
          expect(1, n, "number", "nil")
          if pos > #contents then return nil
          elseif closed then error("attempt to use a closed file", 2)
          elseif n == nil then
              pos = pos + 1
              if isBinary then return contents:byte(pos-1)
              else return contents:sub(pos-1, pos-1) end
          else
              pos = pos + n
              return contents:sub(pos - n, pos - 1)
          end
      end,
      readLine = function()
          if pos > #contents then return nil elseif closed then error("attempt to use a closed file", 2) end
          local retval = ""
          for c in contents:sub(pos):gmatch(".") do
              pos = pos + 1
              if c == '\n' then break end
              retval = retval .. c
          end
          return retval
      end,
      readAll = function()
          if pos > #contents then return nil elseif closed then error("attempt to use a closed file", 2) end
          local retval = contents:sub(pos)
          pos = #contents + 1
          return retval
      end,
      seek = isBinary and function(whence, offset)
          expect(1, whence, "string", "nil")
          expect(2, offset, "number", "nil")
          if closed then error("attempt to use a closed file", 2) end
          whence = whence or "cur"
          offset = offset or 0
          if whence == "set" then pos = offset + 1
          elseif whence == "cur" then pos = pos + offset
          elseif whence == "end" then pos = #contents - offset + 1
          else error("bad argument #1 to 'seek' (invalid option '" .. whence .. "')") end
          return pos - 1
      end or nil,
      close = function()
          if closed then error("attempt to use a closed file", 2) end
          closed = true
          pos = #contents + 1
      end
  } else return {
      write = function(data)
          expect(1, data, "string", "number")
          if closed then error("attempt to use a closed file", 2) end
          if type(data) == "number" then 
              if isBinary then data = string.char(data) or '?'
              else data = tostring(data) end
          end
          contents = contents:sub(1, pos-1) .. data .. contents:sub(pos + #data)
      end,
      writeLine = function(data)
          expect(1, data, "string", "number")
          if closed then error("attempt to use a closed file", 2) end
          if type(data) == "number" then 
              if isBinary then data = string.char(data) or '?'
              else data = tostring(data) end
          end
          data = data .. "\n"
          contents = contents:sub(1, pos-1) .. data .. contents:sub(pos + #data)
      end,
      flush = function()
          if closed then error("attempt to use a closed file", 2) end
          local data = ""
          if not isBinary then for c in contents:gmatch(".") do data = data .. utf8.char(c:byte()) end
          else data = contents end
          local iv = getFilePath(path)
          if iv then iv = {iv:byte(1, 16)} else
              iv = {}
              for i = 1, 16 do iv[i] = math.random(0, 255) end
          end
          local file = orig_fs.open(sha256(fs.combine(path, "") .. iv2bin(iv)), "wb")
          file.write(aeslua.encrypt(key, data, 32, aeslua.CBCMODE, iv, true))
          file.close()
          setFilePath(path, iv2bin(iv))
          saveFileTree()
      end,
      seek = isBinary and function(whence, offset)
          if closed then error("attempt to use a closed file", 2) end
          whence = whence or "cur"
          offset = offset or 0
          if whence == "set" then pos = offset + 1
          elseif whence == "cur" then pos = pos + offset
          elseif whence == "end" then pos = #contents - offset + 1
          else error("bad argument #1 to 'seek' (invalid option '" .. whence .. "')") end
          return pos - 1
      end or nil,
      close = function()
          if closed then error("attempt to use a closed file", 2) end
          local data = ""
          if not isBinary then for c in contents:gmatch(".") do data = data .. utf8.char(c:byte()) end
          else data = contents end
          local iv = getFilePath(path)
          if iv then iv = {iv:byte(1, 16)} else
              iv = {}
              for i = 1, 16 do iv[i] = math.random(0, 255) end
          end
          local file = orig_fs.open(sha256(fs.combine(path, "") .. iv2bin(iv)), "wb")
          file.write(aeslua.encrypt(key, data, 32, aeslua.CBCMODE, iv, true))
          file.close()
          setFilePath(path, iv2bin(iv))
          saveFileTree()
          closed = true
          pos = #contents + 1
      end
  } end
end

local function aux_find(parts, t)
  t = t or filetree
  if #parts == 0 then return t elseif type(t) ~= "table" then return nil end
  local parts2 = {}
  for i,v in ipairs(parts) do parts2[i] = v end
  local name = table.remove(parts2, 1)
  local retval = {}
  for k, v in pairs(t) do if k:match("^" .. name:gsub("([%%%.])", "%%%1"):gsub("%*", "%.%*") .. "$") then retval[k] = aux_find(parts2, v) end end
  return retval
end

local function combineKeys(t, prefix)
  prefix = prefix or ""
  if t == nil then return {} end
  local retval = {}
  for k,v in pairs(t) do
      if type(v) == "string" then table.insert(retval, prefix .. k)
      else for _,w in ipairs(combineKeys(v, prefix .. k .. "/")) do table.insert(retval, w) end end
  end
  return retval
end

function fs.find(wildcard)
  expect(1, wildcard, "string")
  local retval = orig_fs.find(wildcard)
  for _,v in ipairs(combineKeys(aux_find(splitPath(wildcard)))) do table.insert(retval, v) end
  local keep = {}
  for _,v in ipairs(retval) do if not isSHA(fs.getName(v)) then table.insert(keep, v) end end
  retval = keep
  table.sort(retval)
  return retval
end

function fs.attributes(path)
  expect(1, path, "string")
  if orig_fs.exists(path) or filetree == nil then return orig_fs.attributes(path) end
  local data = getFilePath(path)
  local attr
  if data == nil then error("/" .. fs.combine(path, "") .. ": No such file", 2)
  elseif type(data) == "table" then
      attr = orig_fs.attributes("9f721fc36d10270affc7dbba9594e7665f95e0ad6d1729f5d9c0e6cc18235cf3")
      attr.isDir = true
      attr.size = 0
  else
      attr = orig_fs.attributes(sha256(fs.combine(path, "") .. data))
      attr.isDir = false
      attr.size = fs.getSize(path)
  end
  return attr
end

local tEmpty = {}
function fs.complete( sPath, sLocation, bIncludeFiles, bIncludeDirs )
  if type( sPath ) ~= "string" then
      error( "bad argument #1 (expected string, got " .. type( sPath ) .. ")", 2 ) 
  end
  if type( sLocation ) ~= "string" then
      error( "bad argument #2 (expected string, got " .. type( sLocation ) .. ")", 2 ) 
  end
  if bIncludeFiles ~= nil and type( bIncludeFiles ) ~= "boolean" then
      error( "bad argument #3 (expected boolean, got " .. type( bIncludeFiles ) .. ")", 2 ) 
  end
  if bIncludeDirs ~= nil and type( bIncludeDirs ) ~= "boolean" then
      error( "bad argument #4 (expected boolean, got " .. type( bIncludeDirs ) .. ")", 2 ) 
  end
  bIncludeFiles = (bIncludeFiles ~= false)
  bIncludeDirs = (bIncludeDirs ~= false)
  local sDir = sLocation
  local nStart = 1
  local nSlash = string.find( sPath, "[/\\]", nStart )
  if nSlash == 1 then
      sDir = ""
      nStart = 2
  end
  local sName
  while not sName do
      local nSlash = string.find( sPath, "[/\\]", nStart )
      if nSlash then
          local sPart = string.sub( sPath, nStart, nSlash - 1 )
          sDir = fs.combine( sDir, sPart )
          nStart = nSlash + 1
      else
          sName = string.sub( sPath, nStart )
      end
  end

  if fs.isDir( sDir ) then
      local tResults = {}
      if bIncludeDirs and sPath == "" then
          table.insert( tResults, "." )
      end
      if sDir ~= "" then
          if sPath == "" then
              table.insert( tResults, (bIncludeDirs and "..") or "../" )
          elseif sPath == "." then
              table.insert( tResults, (bIncludeDirs and ".") or "./" )
          end
      end
      local tFiles = fs.list( sDir )
      for n=1,#tFiles do
          local sFile = tFiles[n]
          if #sFile >= #sName and string.sub( sFile, 1, #sName ) == sName then
              local bIsDir = fs.isDir( fs.combine( sDir, sFile ) )
              local sResult = string.sub( sFile, #sName + 1 )
              if bIsDir then
                  table.insert( tResults, sResult .. "/" )
                  if bIncludeDirs and #sResult > 0 then
                      table.insert( tResults, sResult )
                  end
              else
                  if bIncludeFiles and #sResult > 0 then
                      table.insert( tResults, sResult )
                  end
              end
          end
      end
      return tResults
  end
  return tEmpty
end

local last_sleep = os.epoch("utc")
function fs.encrypt(from)
    expect(1, from, "string")
    local to = from
    if filetree == nil then error("Cannot encrypt files while locked", 2)
    elseif not orig_fs.exists(from) then error("/" .. fs.combine(from, "") .. ": No such file", 1)
    elseif orig_fs.isDir(from) then error("/" .. fs.combine(from, "") .. ": Is a directory", 2)
    elseif getFilePath(to) ~= nil then error("/" .. fs.combine(to, "") .. ": File exists", 2) end
    local iv = {}
    for i = 1, 16 do iv[i] = math.random(0, 255) end
    local fromfile = orig_fs.open(from, "rb")
    local data = aeslua.encrypt(key, fromfile.readAll(), 32, aeslua.CBCMODE, iv, true)
    fromfile.close()
    orig_fs.delete(from)
    if os.epoch("utc") - last_sleep > 5000 then
        os.queueEvent(os.pullEventRaw())
        last_sleep = os.epoch("utc")
    end
    local tofile, err = orig_fs.open(sha256(fs.combine(to, "") .. iv2bin(iv)), "wb")
    if not tofile then error("Could not write new file: " .. err, 2) end
    tofile.write(data)
    tofile.close()
    setFilePath(to, iv2bin(iv))
    saveFileTree()
end

function fs.decrypt(from, to)
  expect(1, from, "string")
  expect(2, to, "string")
  local iv = getFilePath(from)
  if filetree == nil then error("Cannot decrypt files while locked", 2)
  elseif iv == nil then error("/" .. fs.combine(from, "") .. ": No such file", 2)
  elseif type(iv) == "table" then error("/" .. fs.combine(from, "") .. ": Is a directory", 2)
  elseif orig_fs.exists(to) then error("/" .. fs.combine(to, "") .. ": File exists", 2) end
  local fromfile = orig_fs.open(sha256(fs.combine(from, "") .. iv), "rb")
  local tofile = orig_fs.open(to, "wb")
  tofile.write(aeslua.decrypt(key, fromfile.readAll(), 32, aeslua.CBCMODE, {iv:byte(1, 16)}, true))
  fromfile.close()
  tofile.close()
end

_G.io = {}
do

--- Emulates Lua's standard [io library][io].
--
-- [io]: https://www.lua.org/manual/5.1/manual.html#5.7
--
-- @module io

local type_of = _G.type

--- If we return nil then close the file, as we've reached the end.
-- We use this weird wrapper function as we wish to preserve the varargs
local function checkResult(handle, ...)
  if ... == nil and handle._autoclose and not handle._closed then handle:close() end
  return ...
end

--- A file handle which can be read or written to.
--
-- @type Handle
local handleMetatable
handleMetatable = {
  __name = "FILE*",
  __tostring = function(self)
      if self._closed then
          return "file (closed)"
      else
          local hash = tostring(self._handle):match("table: (%x+)")
          return "file (" .. hash .. ")"
      end
  end,

  __index = {
      --- Close this file handle, freeing any resources it uses.
      --
      -- @treturn[1] true If this handle was successfully closed.
      -- @treturn[2] nil If this file handle could not be closed.
      -- @treturn[2] string The reason it could not be closed.
      -- @throws If this handle was already closed.
      close = function(self)
          if type_of(self) ~= "table" or getmetatable(self) ~= handleMetatable then
              error("bad argument #1 (FILE expected, got " .. type_of(self) .. ")", 2)
          end
          if self._closed then error("attempt to use a closed file", 2) end

          local handle = self._handle
          if handle.close then
              self._closed = true
              handle.close()
              return true
          else
              return nil, "attempt to close standard stream"
          end
      end,

      --- Flush any buffered output, forcing it to be written to the file
      --
      -- @throws If the handle has been closed
      flush = function(self)
          if type_of(self) ~= "table" or getmetatable(self) ~= handleMetatable then
              error("bad argument #1 (FILE expected, got " .. type_of(self) .. ")", 2)
          end
          if self._closed then error("attempt to use a closed file", 2) end

          local handle = self._handle
          if handle.flush then handle.flush() end
          return true
      end,

      lines = function(self, ...)
          if type_of(self) ~= "table" or getmetatable(self) ~= handleMetatable then
              error("bad argument #1 (FILE expected, got " .. type_of(self) .. ")", 2)
          end
          if self._closed then error("attempt to use a closed file", 2) end

          local handle = self._handle
          if not handle.read then return nil, "file is not readable" end

          local args = table.pack(...)
          return function()
              if self._closed then error("file is already closed", 2) end
              return checkResult(self, self:read(table.unpack(args, 1, args.n)))
          end
      end,

      read = function(self, ...)
          if type_of(self) ~= "table" or getmetatable(self) ~= handleMetatable then
              error("bad argument #1 (FILE expected, got " .. type_of(self) .. ")", 2)
          end
          if self._closed then error("attempt to use a closed file", 2) end

          local handle = self._handle
          if not handle.read and not handle.readLine then return nil, "Not opened for reading" end

          local n = select("#", ...)
          local output = {}
          for i = 1, n do
              local arg = select(i, ...)
              local res
              if type_of(arg) == "number" then
                  if handle.read then res = handle.read(arg) end
              elseif type_of(arg) == "string" then
                  local format = arg:gsub("^%*", ""):sub(1, 1)

                  if format == "l" then
                      if handle.readLine then res = handle.readLine() end
                  elseif format == "L" and handle.readLine then
                      if handle.readLine then res = handle.readLine(true) end
                  elseif format == "a" then
                      if handle.readAll then res = handle.readAll() or "" end
                  elseif format == "n" then
                      res = nil -- Skip this format as we can't really handle it
                  else
                      error("bad argument #" .. i .. " (invalid format)", 2)
                  end
              else
                  error("bad argument #" .. i .. " (expected string, got " .. type_of(arg) .. ")", 2)
              end

              output[i] = res
              if not res then break end
          end

          -- Default to "l" if possible
          if n == 0 and handle.readLine then return handle.readLine() end
          return table.unpack(output, 1, n)
      end,

      seek = function(self, whence, offset)
          if type_of(self) ~= "table" or getmetatable(self) ~= handleMetatable then
              error("bad argument #1 (FILE expected, got " .. type_of(self) .. ")", 2)
          end
          if self._closed then error("attempt to use a closed file", 2) end

          local handle = self._handle
          if not handle.seek then return nil, "file is not seekable" end

          -- It's a tail call, so error positions are preserved
          return handle.seek(whence, offset)
      end,

      setvbuf = function(self, mode, size) end,

      --- Write one or more values to the file
      --
      -- @tparam string|number ... The values to write.
      -- @treturn[1] Handle The current file, allowing chained calls.
      -- @treturn[2] nil If the file could not be written to.
      -- @treturn[2] string The error message which occurred while writing.
      write = function(self, ...)
          if type_of(self) ~= "table" or getmetatable(self) ~= handleMetatable then
              error("bad argument #1 (FILE expected, got " .. type_of(self) .. ")", 2)
          end
          if self._closed then error("attempt to use a closed file", 2) end

          local handle = self._handle
          if not handle.write then return nil, "file is not writable" end

          for i = 1, select("#", ...) do
              local arg = select(i, ...)
              expect(i, arg, "string", "number")
              handle.write(arg)
          end
          return self
      end,
  },
}

local defaultInput = setmetatable({
  _handle = { readLine = _G.read },
}, handleMetatable)

local defaultOutput = setmetatable({
  _handle = { write = _G.write },
}, handleMetatable)

local defaultError = setmetatable({
  _handle = {
      write = function(...)
          local oldColour
          if term.isColour() then
              oldColour = term.getTextColour()
              term.setTextColour(colors.red)
          end
          _G.write(...)
          if term.isColour() then term.setTextColour(oldColour) end
      end,
  },
}, handleMetatable)

local currentInput = defaultInput
local currentOutput = defaultOutput

--- A file handle representing the "standard input". Reading from this
-- file will prompt the user for input.
io.stdin = defaultInput

--- A file handle representing the "standard output". Writing to this
-- file will display the written text to the screen.
io.stdout = defaultOutput

--- A file handle representing the "standard error" stream.
--
-- One may use this to display error messages, writing to it will display
-- them on the terminal.
io.stderr = defaultError

--- Closes the provided file handle.
--
-- @tparam[opt] Handle file The file handle to close, defaults to the
-- current output file.
--
-- @see Handle:close
-- @see io.output
function io.close(file)
  if file == nil then return currentOutput:close() end

  if type_of(file) ~= "table" or getmetatable(file) ~= handleMetatable then
      error("bad argument #1 (FILE expected, got " .. type_of(file) .. ")", 2)
  end
  return file:close()
end

--- Flushes the current output file.
--
-- @see Handle:flush
-- @see io.output
function io.flush()
  return currentOutput:flush()
end

--- Get or set the current input file.
--
-- @tparam[opt] Handle|string file The new input file, either as a file path or pre-existing handle.
-- @treturn Handle The current input file.
-- @throws If the provided filename cannot be opened for reading.
function io.input(file)
  if type_of(file) == "string" then
      local res, err = open(file, "rb")
      if not res then error(err, 2) end
      currentInput = res
  elseif type_of(file) == "table" and getmetatable(file) == handleMetatable then
      currentInput = file
  elseif file ~= nil then
      error("bad fileument #1 (FILE expected, got " .. type_of(file) .. ")", 2)
  end

  return currentInput
end

--- Opens the given file name in read mode and returns an iterator that,
-- each time it is called, returns a new line from the file.
--
-- This can be used in a for loop to iterate over all lines of a file:
--
-- ```lua
-- for line in io.lines(filename) do print(line) end
-- ```
--
-- Once the end of the file has been reached, @{nil} will be
-- returned. The file is automatically closed.
--
-- If no file name is given, the @{io.input|current input} will be used
-- instead. In this case, the handle is not used.
--
-- @tparam[opt] string filename The name of the file to extract lines from
-- @param ... The argument to pass to @{Handle:read} for each line.
-- @treturn function():string|nil The line iterator.
-- @throws If the file cannot be opened for reading
--
-- @see Handle:lines
-- @see io.input
function io.lines(filename, ...)
  expect(1, filename, "string", "nil")
  if filename then
      local ok, err = open(filename, "rb")
      if not ok then error(err, 2) end

      -- We set this magic flag to mark this file as being opened by io.lines and so should be
      -- closed automatically
      ok._autoclose = true
      return ok:lines(...)
  else
      return currentInput:lines(...)
  end
end

--- Open a file with the given mode, either returning a new file handle
-- or @{nil}, plus an error message.
--
-- The `mode` string can be any of the following:
--  - **"r"**: Read mode
--  - **"w"**: Write mode
--  - **"w"**: Append mode
--
-- The mode may also have a `b` at the end, which opens the file in "binary
-- mode". This allows you to read binary files, as well as seek within a file.
--
-- @tparam string filename The name of the file to open.
-- @tparam[opt] string mode The mode to open the file with. This defaults to `rb`.
-- @treturn[1] Handle The opened file.
-- @treturn[2] nil In case of an error.
-- @treturn[2] string The reason the file could not be opened.
function io.open(filename, mode)
  expect(1, filename, "string")
  expect(2, mode, "string", "nil")

  local sMode = mode and mode:gsub("%+", "") or "rb"
  local file, err = fs.open(filename, sMode)
  if not file then return nil, err end

  return setmetatable({ _handle = file }, handleMetatable)
end

--- Get or set the current output file.
--
-- @tparam[opt] Handle|string file The new output file, either as a file path or pre-existing handle.
-- @treturn Handle The current output file.
-- @throws If the provided filename cannot be opened for writing.
function io.output(file)
  if type_of(file) == "string" then
      local res, err = open(file, "wb")
      if not res then error(err, 2) end
      currentOutput = res
  elseif type_of(file) == "table" and getmetatable(file) == handleMetatable then
      currentOutput = file
  elseif file ~= nil then
      error("bad argument #1 (FILE expected, got " .. type_of(file) .. ")", 2)
  end

  return currentOutput
end

--- Read from the currently opened input file.
--
-- This is equivalent to `io.input():read(...)`. See @{Handle:read|the
-- documentation} there for full details.
--
-- @tparam string ... The formats to read, defaulting to a whole line.
-- @treturn (string|nil)... The data read, or @{nil} if nothing can be read.
function io.read(...)
  return currentInput:read(...)
end

--- Checks whether `handle` is a given file handle, and determine if it is open
-- or not.
--
-- @param obj The value to check
-- @treturn string|nil `"file"` if this is an open file, `"closed file"` if it
-- is a closed file handle, or `nil` if not a file handle.
function io.type(obj)
  if type_of(obj) == "table" and getmetatable(obj) == handleMetatable then
      if obj._closed then
          return "closed file"
      else
          return "file"
      end
  end
  return nil
end

--- Write to the currently opened output file.
--
-- This is equivalent to `io.output():write(...)`. See @{Handle:write|the
-- documentation} there for full details.
--
-- @tparam string ... The strings to write
function io.write(...)
  return currentOutput:write(...)
end

end

-- Hide the upvalues of the FS library since they could cause data leakage
-- This is the most advanced hiding we're doing; more protection can be offered by other tools
if debug then
  local native_getupvalue, native_setupvalue = debug.getupvalue, debug.setupvalue
  local getupvalue, setupvalue
  function getupvalue(func, up)
      if func == getupvalue then return nil end
      for _,v in pairs(fs) do if func == v then return nil end end
      return native_getupvalue(func, up)
  end
  function setupvalue(func, up, val)
      if func == setupvalue then return nil end
      for _,v in pairs(fs) do if func == v then return nil end end
      return native_setupvalue(func, up, val)
  end
  debug.getupvalue = getupvalue
  debug.setupvalue = setupvalue
end