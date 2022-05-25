if not fs.encrypt then
    shell.run("cc-lock/fsencrypt")
end

local banned_files = {
    ["register.lua"]={dir=false},
    ["cc-lock"]={dir=true},
    ["rom"]={dir=true},
    ["GuiH"]={dir=true},
    [".credentials"]={dir=false},
    ["startup/cc-lock.lua"]={dir=false}
}

local function drawBorder(frame, title)
    local win = frame.window
    local width, height = frame.positioning.width, frame.positioning.height
    for y=1, height do
        win.setCursorPos(1, y)
        win.blit("\149", "0", "f")
        win.setCursorPos(width, y)
        win.blit("\149", "f", "0")
    end
    win.setCursorPos(1, 1)
    win.blit((" "):rep(width), ("f"):rep(width), ("8"):rep(width))
    win.setCursorPos(1, height)
    win.blit(("\143"):rep(width), ("f"):rep(width), ("0"):rep(width))
    win.setCursorPos(1, height)
    win.blit("\138", "f", "0")
    win.setCursorPos(width, height)
    win.blit("\133", "f", "0")
    win.setCursorPos(2, 1)
    win.setTextColor(colors.black)
    win.setBackgroundColor(colors.lightGray)
    win.write(title)
    win.setTextColor(colors.white)
    win.setBackgroundColor(colors.black)
end

local function createWindow(gui, data)
    local title = data.title or "unamed"
    local width = data.width or 10
    local height = data.height or 10

    local frame = gui.create.frame(
        {
            name=title,
            x=data.x or 1, y=data.y or 1,
            width=width,
            height=height,
        }  
    )
    local child = frame.child
    local stopper = {running = true}
    drawBorder(frame, title)

    local sub = frame.child.create.frame({
        draggable=false,
        x=2, y=2, width=width-2, height=height-2,
    })

    child.create.button({
        name=frame.name .. "QuitButton",
        text=child.text({text="x",blit={"E", "8"}}),
        x=width-1, y=1, width=1, height=1,
        on_click = data.on_quit or function(component)
            print("hue?")
        end
    })
    
    child.create.button({
        name=frame.name .. "MinimizetButton",
        text=child.text({text="_",blit={"1", "8"}}),
        x=width-3, y=1, width=1, height=1,
        on_click = data.on_reduce or function(component)
            frame.visible=false
        end
    })

    child.create.button({
        name=frame.name .. "MaximiseButton",
        text=child.text({text="\23",blit={"D", "8"}}),
        x=width-5, y=1, width=1, height=1,
        on_click = data.on_maximise or function(component) end
    })

    return frame, sub
end

local function go_paths_encrypted(path,f)
    local files = fs.list(path or "")
    for k,v in pairs(files) do
        local path = fs.combine(path,v)
        if not fs.isDir(path) then
            if not banned_files[path] then
                f(path)
            end
        elseif not (banned_files[path] or {}).dir then
            go_paths_encrypted(path,f)
        end
    end
end

return {
    createWindow = createWindow,
    go_paths_encrypted=go_paths_encrypted
}
