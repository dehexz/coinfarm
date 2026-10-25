local Players = game:GetService("Players")
local UIS = game:GetService("UserInputService")
local plr = Players.LocalPlayer
 
local OFFSET = 0          -- studs below the coin to travel at
local FIRST_SPEED = 999   -- first coin of the round is a fast snap
local MENU_KEY = 0x70     -- F1
local HEALTH_OFFSET = 0x184 -- Humanoid health offset for memory_write (changes when Roblox updates)

-- Position-based death detection (for Infection and any mode where "Alive" is unreliable).
-- If our character ends up more than this many studs from where we last put it, we were
-- killed / infected / teleported by the game.
local TELEPORT_DIST = 40
local POS_FRESH = 0.3     -- only trust the comparison if we wrote a position this recently (seconds)

local MOUSE_Y_OFFSET = 0             -- only applies to the fallback mouse method; leave at 0
local MOUSE_MENU = true              -- false = menu is display-only, no mouse reading/clicking at all (F1-F5 still work)
local FRIEND_STOP = true             -- default state of the friend-stop feature
local CHECK_EXISTING_FRIENDS = false -- true = also stop if a friend is already in the server at load
local FRIEND_NAMES = {}              -- fallback list if IsFriendsWith doesn't work, e.g. {"MyFriend1", "MyFriend2"}
 
local first = true
local missed = 0         -- consecutive coins we reached but couldn't collect
local lastResetTry = 0
local noCoinSince = nil
local noCoinResetDone = false -- send Esc, R, Enter once after the coin container stays empty
local status = "Starting"
local lifeChar = nil     -- character we last farmed with
local lastContainerSeen = nil -- coin container from the previous step (map change detector)
local lastEvent = "-"        -- shown in the menu: the last notable thing the script did
local wasAlive = false
local freezeUntil = 0        -- hold still while the game swaps maps / characters
local heartbeat = tick()     -- updated by the farm loop; the watchdog restarts the loop if it stalls
local teleportFlag = false   -- set when position tracking decides we were moved/killed
local lastSetPos, lastSetTime = nil, 0 -- last position the script wrote to the character
 
-- Settings (changed from the Drawing menu below)
local cfg = {
    enabled = true,
    autoReset = true,
    speed = 20,
    friendStop = FRIEND_STOP,
}
 
local function getEnabled() return cfg.enabled end
local function getAutoReset() return cfg.autoReset end
local function getSpeed() return cfg.speed end
 
------------------------------------------------------------
-- Performance helpers
------------------------------------------------------------
local ZERO = Vector3.new(0, 0, 0)
local function zeroVel(part) part.Velocity = ZERO end
 
local lastProps = {}
local function setp(obj, key, value)
    local c = lastProps[obj]
    if not c then
        c = {}
        lastProps[obj] = c
    end
    if c[key] ~= value then
        c[key] = value
        obj[key] = value
    end
end
 
------------------------------------------------------------
-- Farm logic
------------------------------------------------------------
-- pcall'd: reading a deleted instance (old map) can throw in an external VM
local function getParent(o) return o.Parent end
local function isValid(obj)
    if obj == nil then return false end
    local ok, parent = pcall(getParent, obj)
    return ok and parent ~= nil
end
 
-- Uses the "Alive" attribute; falls back to Humanoid health if it isn't set.
local function isAlive()
    local attr = plr:GetAttribute("Alive")
    if attr == false then return false end

    -- Don't trust the attribute alone: in Infection it can stay true after you are
    -- infected/killed, so Humanoid health is checked as well.
    local char = plr.Character
    local hum = char and char:FindFirstChild("Humanoid")
    if hum then
        local ok, hp = pcall(function() return hum.Health end)
        if ok and type(hp) == "number" and hp <= 0 then return false end
    end

    if attr == true then return true end
    return hum ~= nil
end
 
local function dist(a, b)
    local dx, dy, dz = a.X - b.X, a.Y - b.Y, a.Z - b.Z
    return math.sqrt(dx * dx + dy * dy + dz * dz)
end
 
-- Every position the script writes is remembered; if the real position is far from it a
-- moment later, the game moved us (death, infection, round end).
local function setPos(hrp, v)
    lastSetPos, lastSetTime = v, tick()
    hrp.Position = v
end
 
local function wasTeleported(hrp)
    if not lastSetPos or tick() - lastSetTime > POS_FRESH then return false end
    local ok, p = pcall(function() return hrp.Position end)
    if not ok or not p then return false end
    return dist(p, lastSetPos) > TELEPORT_DIST
end
 
local noclipChar, noclipParts = nil, {}
local lastNoclip, lastNoclipRebuild = 0, 0
 
local function setNoclip()
    local now = tick()
    if now - lastNoclip < 0.2 then return end
    lastNoclip = now
 
    local char = plr.Character
    if not char then return end
 
    if char ~= noclipChar or now - lastNoclipRebuild > 2 then
        noclipChar, noclipParts, lastNoclipRebuild = char, {}, now
        for _, part in ipairs(char:GetChildren()) do
            if part:IsA("BasePart") then
                noclipParts[#noclipParts + 1] = part
            end
        end
    end
 
    for _, part in ipairs(noclipParts) do
        pcall(function() part.CanCollide = false end)
    end
end
 
local cachedContainer = nil
local lastContainer = nil
local lastScan = 0
 
-- Containers we are DONE with (we died / reset / round ended / coins don't register).
-- A finished map can linger in workspace through the lobby and map voting, so it must
-- never be farmed again. A brand new map's container is never in this list.
local function evt(msg)
    lastEvent = string.sub(tostring(msg), 1, 30)
end
 
local usedContainers = {}
local function isUsed(c)
    for _, u in ipairs(usedContainers) do
        if u == c then return true end
    end
    return false
end
local function markUsed(c, why)
    if c == nil or isUsed(c) then return end
    usedContainers[#usedContainers + 1] = c
    if #usedContainers > 12 then table.remove(usedContainers, 1) end
    cachedContainer = nil
    evt("used: " .. tostring(why))
end
 
local function hasCoins(container)
    for _, obj in ipairs(container:GetChildren()) do
        if obj.Name == "Coin_Server" then return true end
    end
    return false
end
 
-- Old maps can linger in workspace, so prefer a CoinContainer that really
-- has coins in it, and re-scan whenever the cached one goes empty/stale.
local function findCoinContainer()
    if isValid(cachedContainer) and not isUsed(cachedContainer) then return cachedContainer end
    cachedContainer = nil
    if tick() - lastScan < 1 then
        return (isValid(lastContainer) and not isUsed(lastContainer)) and lastContainer or nil
    end
    lastScan = tick()
 
    local found, fallback = nil, nil
    local ok, kids = pcall(function() return workspace:GetChildren() end)
    if ok and kids then
        for _, obj in ipairs(kids) do
            pcall(function()
                if found == nil and obj.ClassName == "Model" then
                    local container = obj:FindFirstChild("CoinContainer")
                    if container and not isUsed(container) then
                        if hasCoins(container) then
                            found = container
                        else
                            fallback = fallback or container
                        end
                    end
                end
            end)
            if found then break end
        end
    end
    local result = found or fallback
    cachedContainer, lastContainer = result, result or lastContainer
    return result
end
 
-- Tries Health = 0 first, then the Roblox menu reset, until the character dies.
local function resetCharacter()
    local char = plr.Character
    if not char then return false end
    local hum = char:FindFirstChildOfClass("Humanoid") or char:FindFirstChild("Humanoid")
    lastSetPos = nil -- the void fall below is intentional, don't read it as a teleport
 
    -- 1) Health = 0, plus a direct memory write to the health offset (needs
    --    "Unsafe LuaU Execution Allowed"; works while Roblox is unfocused)
    if hum then
        pcall(function() hum.Health = 0 end)
        pcall(function()
            if hum.Address then
                memory_write("float", hum.Address + HEALTH_OFFSET, -10)
            end
        end)
    end
    wait(0.5)
    if not isAlive() then return true end
 
    -- 2) Fall into the void. Needs no keyboard and no window focus (position writes
    --    are what the farming itself uses), so it works while Roblox is in the background.
    local hrp = char:FindFirstChild("HumanoidRootPart")
    if hrp then
        for _ = 1, 40 do
            heartbeat = tick()
            local okp = pcall(function()
                local p = hrp.Position
                hrp.Position = Vector3.new(p.X, -2000, p.Z)
            end)
            if not okp then break end
            wait(0.1)
            if not isAlive() then return true end
        end
    end
 
    -- 3) Roblox menu reset: Esc, R, Enter. Only when Roblox is the focused window,
    --    otherwise these keys would be typed into whatever app you are looking at.
    if isrbxactive() then
        pcall(function()
            keypress(0x1B) wait(0.1) keyrelease(0x1B) wait(0.3)
            keypress(0x52) wait(0.1) keyrelease(0x52) wait(0.3)
            keypress(0x0D) wait(0.1) keyrelease(0x0D)
        end)
        for _ = 1, 20 do
            wait(0.1)
            if not isAlive() then return true end
        end
    end
    return false
end
 
local function getClosestCoin(container, origin)
    local best, bestDist = nil, math.huge
    for _, obj in ipairs(container:GetChildren()) do
        if obj.Name == "Coin_Server" and obj:FindFirstChild("TouchInterest") then
            local d = dist(obj.Position, origin)
            if d < bestDist then
                best, bestDist = obj, d
            end
        end
    end
    return best
end
 
-- Moves hrp toward coin. Returns true only if we arrived while the coin was still up for grabs.
local function tween(hrp, coin, spd)
    local sp = hrp.Position
    local tp = coin.Position
    local sx, sy, sz = sp.X, sp.Y - OFFSET, sp.Z
    local tx, ty, tz = tp.X, tp.Y - OFFSET, tp.Z
 
    local duration = math.max(dist(sp, tp) / spd, 0.05)
    local t0 = tick()
    local lastCheck = 0
 
    while true do
        local now = tick()
        heartbeat = now
 
        if not isValid(hrp) or not isValid(coin) or not getEnabled() then
            return false
        end
 
        -- Slower checks (every 0.1s): alive state and coin still up for grabs
        if now - lastCheck > 0.1 then
            lastCheck = now
            if not isAlive() then return false end
            if wasTeleported(hrp) then
                teleportFlag = true
                return false
            end
            if not coin:FindFirstChild("TouchInterest") then
                return false
            end
            pcall(zeroVel, hrp)
        end
 
        local alpha = (now - t0) / duration
        if alpha >= 1 then break end
 
        setNoclip()
        setPos(hrp, Vector3.new(
            sx + (tx - sx) * alpha,
            sy + (ty - sy) * alpha,
            sz + (tz - sz) * alpha
        ))
        wait()
    end
 
    if isValid(hrp) and isValid(coin) and coin:FindFirstChild("TouchInterest") then
        setPos(hrp, coin.Position)
        return true
    end
    return false
end
 
-- Resets the character. Retries every 3s until the character actually dies.
local function doReset(reason)
    if not getAutoReset() or tick() - lastResetTry < 3 then
        return false
    end
    lastResetTry = tick()
    status = "Resetting"
    evt("reset: " .. tostring(reason))
    if resetCharacter() then
        markUsed(lastContainerSeen, "reset")
        notify(reason .. ", reset done", "Coin Farm", 2)
        return true
    end
    warn("[CoinFarm] Reset failed, will retry")
    return false
end
 
local function step()
    if not getEnabled() then
        noCoinSince = nil
        -- keep the "friend joined" status visible instead of overwriting it
        if status ~= "Stopped: friend joined" then
            status = "Disabled"
        end
        return wait(0.25)
    end
 
    -- Position tracking caught a kill / infection / teleport: treat it exactly like a death
    if teleportFlag then
        teleportFlag = false
        markUsed(lastContainerSeen, "moved/killed")
        wasAlive = false
        first, missed, noCoinSince = true, 0, nil
        lastSetPos = nil
        freezeUntil = tick() + 2
        status = "Teleported/dead"
        return wait(0.25)
    end
 
    if not isAlive() then
        markUsed(lastContainerSeen, "dead")
        wasAlive = false
        first, missed, noCoinSince = true, 0, nil
        lastSetPos = nil
        status = "Dead"
        return wait(0.25)
    end
 
    if not wasAlive then
        wasAlive = true
        freezeUntil = tick() + 2
        evt("alive, settling")
    end
 
    -- New character (new round / respawn): forget the old life
    if plr.Character ~= lifeChar then
        lifeChar = plr.Character
        missed = 0
        first, noCoinSince, cachedContainer = true, nil, nil
        lastSetPos = nil
    end
 
    local container = findCoinContainer()
 
    -- Container changed or vanished = old map deleted / new one loaded: clean slate
    if container ~= lastContainerSeen then
        lastContainerSeen = container
        missed = 0
        first, noCoinSince = true, nil
        noCoinResetDone = false
        if container then
            freezeUntil = tick() + 2
            evt("new map, settling")
        end
    end
 
    -- Give the game a moment after a map swap / respawn before touching anything
    if tick() < freezeUntil then
        status = "Settling"
        return wait(0.2)
    end
 
    -- Missed coin pickups no longer trigger an automatic reset.
 
    if not container then
        status = "No coin container"
        return wait(0.25)
    end
 
    local char = plr.Character
    local hrp = char and char:FindFirstChild("HumanoidRootPart")
    if not hrp then
        status = "No character"
        return wait(0.25)
    end
 
    local coin = getClosestCoin(container, hrp.Position)
    if not coin then
        noCoinSince = noCoinSince or tick()
        cachedContainer = nil -- may be stale (new round/new map), re-scan
        status = "No coins"

        -- If the map has stayed empty for 2 seconds, request a Roblox reset
        -- with Esc -> R -> Enter. Only send keys while Roblox is focused.
        if not noCoinResetDone and tick() - noCoinSince >= 2 then
            noCoinResetDone = true
            if isrbxactive() then
                pcall(function()
                    keypress(0x1B) wait(0.1) keyrelease(0x1B) wait(0.3)
                    keypress(0x52) wait(0.1) keyrelease(0x52) wait(0.3)
                    keypress(0x0D) wait(0.1) keyrelease(0x0D)
                end)
                status = "Round ended - reset requested"
                evt("round ended: Esc R Enter")
            else
                evt("round ended: Roblox not focused; reset skipped")
            end
        end
        return wait(0.1)
    end
    noCoinSince = nil
    noCoinResetDone = false
 
    status = "Farming"
    setNoclip()
    local spd = first and FIRST_SPEED or getSpeed()
    if tween(hrp, coin, spd) then
        first = false
 
        -- Stay on the coin until the server removes it (scaled by ping),
        -- so the touch actually registers before we move on.
        local ping = 0
        pcall(function() ping = tonumber(GetPingValue()) or 0 end)
        local deadline = tick() + math.min(1.5, 0.3 + (ping / 1000) * 2)
        local cp = coin.Position
        local got = false
 
        while tick() < deadline do
            if not isValid(coin) or not coin:FindFirstChild("TouchInterest") then
                got = true
                break
            end
            if not isValid(hrp) or not isAlive() or not getEnabled() then break end
            if wasTeleported(hrp) then
                teleportFlag = true
                break
            end
            setPos(hrp, cp)
            heartbeat = tick()
            wait()
        end
 
        if got then
            missed = 0
        elseif not teleportFlag and isAlive() and getEnabled() then
            missed = missed + 1
        end
    end
    wait()
end
 
------------------------------------------------------------
-- Drawing menu (F1 show/hide, drag the title area to move)
-- Hotkeys: F2 farm, F3 auto reset, F4/F5 speed -/+
------------------------------------------------------------
local MENU_W, MENU_H, DRAG_H = 240, 272, 40
local menuX, menuY = 120, 120
local menuVisible = true
 
local C_SHADOW = Color3.fromRGB(0, 0, 0)
local C_BG     = Color3.fromRGB(22, 22, 29)
local C_ROW    = Color3.fromRGB(33, 33, 44)
local C_BTN    = Color3.fromRGB(52, 52, 70)
local C_BTN_HI = Color3.fromRGB(78, 78, 104)
local C_ACCENT = Color3.fromRGB(135, 100, 255)
local C_TEXT   = Color3.fromRGB(238, 238, 245)
local C_DIM    = Color3.fromRGB(150, 150, 168)
local C_ON     = Color3.fromRGB(70, 200, 120)
local C_OFF    = Color3.fromRGB(205, 75, 85)
 
local elements = {}   -- { obj, rx, ry }
local updaters = {}   -- run every frame while visible
local hits = {}       -- clickable regions
local warnedProps = {}
 
local function draw(kind, rx, ry, props, z)
    local d = Drawing.new(kind)
    pcall(function() d.Transparency = 1 end)
    for k, v in pairs(props) do
        local ok = pcall(function() d[k] = v end)
        if not ok and not warnedProps[k] then
            warnedProps[k] = true
            warn("[CoinFarm] Unsupported " .. kind .. " property: " .. tostring(k))
        end
    end
    if kind == "Text" then
        if not pcall(function() d.FontSize = 14 end) then
            pcall(function() d.Size = 14 end)
        end
    end
    pcall(function() d.ZIndex = z or 1 end)
    d.Visible = false
    local e = { obj = d, rx = rx, ry = ry }
    elements[#elements + 1] = e
    return d, e
end
 
local function rect(rx, ry, w, h, color, corner, z, transparency)
    return draw("Square", rx, ry, {
        Size = Vector2.new(w, h), Filled = true, Color = color,
        Corner = corner or 0, Transparency = transparency or 1,
    }, z)
end
 
local function label(text, rx, ry, color)
    return draw("Text", rx, ry, { Text = text, Color = color or C_TEXT, Outline = false, Center = false }, 6)
end
 
local function centerText(text, rx, ry, color)
    return draw("Text", rx, ry, { Text = text, Color = color or C_TEXT, Outline = false, Center = true }, 6)
end
 
local function hit(rx, ry, w, h, fn, obj, base, hover)
    hits[#hits + 1] = { rx = rx, ry = ry, w = w, h = h, fn = fn, obj = obj, base = base, hover = hover }
end
 
local function addToggle(text, ry, key)
    rect(10, ry, MENU_W - 20, 30, C_ROW, 8, 2)
    label(text, 22, ry + 8)
    local tx = MENU_W - 62
    local track = rect(tx, ry + 6, 40, 18, C_OFF, 9, 3)
    local _, knobE = draw("Circle", tx + 9, ry + 15, {
        Radius = 7, Filled = true, NumSides = 24, Color = C_TEXT,
    }, 4)
    hit(10, ry, MENU_W - 20, 30, function() cfg[key] = not cfg[key] end)
    updaters[#updaters + 1] = function()
        local on = cfg[key]
        setp(track, "Color", on and C_ON or C_OFF)
        knobE.rx = tx + (on and 31 or 9)
    end
end
 
-- Shadow, panel, title
rect(3, 5, MENU_W, MENU_H, C_SHADOW, 14, 0, 0.35)
rect(0, 0, MENU_W, MENU_H, C_BG, 14, 1)
label("Coin Farm", 16, 11, C_TEXT)
label("F1", MENU_W - 32, 11, C_DIM)
rect(16, 34, MENU_W - 32, 2, C_ACCENT, 1, 2)
 
addToggle("Farm", 46, "enabled")
addToggle("Auto Reset", 82, "autoReset")
addToggle("Friend Stop", 118, "friendStop")
 
-- Speed row
rect(10, 154, MENU_W - 20, 30, C_ROW, 8, 2)
label("Speed", 22, 162)
local minus = rect(MENU_W - 112, 159, 26, 20, C_BTN, 6, 3)
centerText("-", MENU_W - 99, 162)
local plus = rect(MENU_W - 44, 159, 26, 20, C_BTN, 6, 3)
centerText("+", MENU_W - 31, 162)
local speedText = centerText("", MENU_W - 65, 162)
local function changeSpeed(delta)
    cfg.speed = math.max(5, math.min(60, cfg.speed + delta))
end
hit(MENU_W - 112, 159, 26, 20, function() changeSpeed(-5) end, minus, C_BTN, C_BTN_HI)
hit(MENU_W - 44, 159, 26, 20, function() changeSpeed(5) end, plus, C_BTN, C_BTN_HI)
updaters[#updaters + 1] = function() setp(speedText, "Text", tostring(cfg.speed)) end
 
-- Status
local statusText = label("", 16, 200, C_DIM)
local hintText = label("F2-F5 hotkeys", 16, 220, C_DIM)
local evtText = label("", 16, 240, C_DIM)
updaters[#updaters + 1] = function() setp(evtText, "Text", "Last: " .. lastEvent) end
updaters[#updaters + 1] = function()
    setp(statusText, "Text", "Status: " .. status)
end
 
local function setMenuVisible(state)
    for _, e in ipairs(elements) do
        e.obj.Visible = state
    end
end
 
local function layout()
    for _, e in ipairs(elements) do
        local x, y = menuX + e.rx, menuY + e.ry
        if e.lx ~= x or e.ly ~= y then
            e.lx, e.ly = x, y
            e.obj.Position = Vector2.new(x, y)
        end
    end
end
 
-- Same method the AR2 script uses: Player:GetMouse() is already in the same
-- coordinate space as Drawing objects, so no height correction is needed.
local mouseObj = nil
local function getMouse()
    if not MOUSE_MENU then return nil, nil end
    if not mouseObj then
        pcall(function() mouseObj = plr:GetMouse() end)
    end
    if mouseObj then
        local ok, x, y = pcall(function() return mouseObj.X, mouseObj.Y end)
        if ok and type(x) == "number" and type(y) == "number" and x == x and y == y then
            return x, y
        end
    end
    -- fallback: UserInputService (includes the 36px top bar, so subtract it)
    local ok, pos = pcall(function() return UIS:GetMouseLocation() end)
    if ok and pos then return pos.X, pos.Y - 36 - MOUSE_Y_OFFSET end
    return nil, nil
end
 
local function inRect(mx, my, x, y, w, h)
    return mx >= x and mx <= x + w and my >= y and my <= y + h
end
 
local hotkeys = {
    { 0x71, function() cfg.enabled = not cfg.enabled end },
    { 0x72, function() cfg.autoReset = not cfg.autoReset end },
    { 0x73, function() changeSpeed(-5) end },
    { 0x74, function() changeSpeed(5) end },
}
 
local wasF1, wasDown, dragging = false, false, false
local wasActive, activeSince = false, 0
local wasKey = {}
local dragOX, dragOY = 0, 0
local warnedMouse = false
 
local function menuStep()
    local active = isrbxactive()
    if active and not wasActive then activeSince = tick() end
    wasActive = active
 
    local f1 = active and iskeypressed(MENU_KEY)
    if f1 and not wasF1 then
        menuVisible = not menuVisible
        setMenuVisible(menuVisible)
    end
    wasF1 = f1 and true or false
 
    if active then
        for _, hk in ipairs(hotkeys) do
            local keyCode = hk[1]
            local action = hk[2]
            local pressed = iskeypressed(keyCode) and true or false
            if pressed and not wasKey[keyCode] then action() end
            wasKey[keyCode] = pressed
        end
    end
 
    if not menuVisible then
        dragging = false
        return
    end
 
    for _, fn in ipairs(updaters) do fn() end
 
    local mx, my = getMouse()
    if mx then
        setp(hintText, "Text", "F2-F5 hotkeys")
    else
        setp(hintText, "Text", MOUSE_MENU and "Mouse N/A - use F2-F5" or "Mouse off - use F2-F5")
        if MOUSE_MENU and not warnedMouse then
            warnedMouse = true
            warn("[CoinFarm] Could not read mouse position; use F2-F5 hotkeys.")
        end
    end
 
    -- Only accept clicks while the Roblox window is focused
    local down = active and (mx ~= nil) and ismouse1pressed() and true or false
 
    -- hover highlight
    for _, h in ipairs(hits) do
        if h.obj then
            local over = mx and inRect(mx, my, menuX + h.rx, menuY + h.ry, h.w, h.h)
            setp(h.obj, "Color", over and h.hover or h.base)
        end
    end
 
    -- Ignore clicks for 0.6s after Roblox gains focus, so the click you use to
    -- refocus the window can't hit a menu toggle by accident.
    local clickOK = tick() - activeSince > 0.6
    if down and not wasDown and clickOK then
        if inRect(mx, my, menuX, menuY, MENU_W, DRAG_H) then
            dragging = true
            dragOX, dragOY = mx - menuX, my - menuY
        else
            for _, h in ipairs(hits) do
                if inRect(mx, my, menuX + h.rx, menuY + h.ry, h.w, h.h) then
                    h.fn()
                    break
                end
            end
        end
    elseif down and dragging then
        menuX, menuY = mx - dragOX, my - dragOY
    end
    if not down then dragging = false end
    wasDown = down
 
    layout()
end
 
layout()
setMenuVisible(true)
 
task.spawn(function()
    while true do
        local ok, err = pcall(menuStep)
        if not ok then
            warn("[CoinFarm menu] " .. tostring(err))
            wait(1)
        end
        wait(menuVisible and 0.03 or 0.05)
    end
end)
 
-- Farm loop. Restartable: if an old copy is stuck, a new generation takes over.
local farmGen = 0
local function startFarmLoop()
    farmGen = farmGen + 1
    local myGen = farmGen
    task.spawn(function()
        while myGen == farmGen do
            heartbeat = tick()
            local ok, err = pcall(step)
            if not ok then
                warn("[CoinFarm] " .. tostring(err))
                lastEvent = "err: " .. string.sub(tostring(err), 1, 24)
                wait(1)
            end
        end
    end)
end
startFarmLoop()
 
-- Watchdog: if the farm loop hasn't ticked in 12s it is stuck or dead, so restart it.
task.spawn(function()
    while true do
        wait(2)
        if tick() - heartbeat > 12 then
            evt("watchdog restart")
            heartbeat = tick()
            cachedContainer = nil
            first = true
            noCoinSince = nil
            missed = 0
            startFarmLoop()
        end
    end
end)

------------------------------------------------------------
-- Friend watcher: stops the farm when a friend joins.
-- It never re-enables the farm; that needs a manual toggle / F2.
------------------------------------------------------------
-- Automatic friend detection: Matcha has no IsFriendsWith, so we download your
-- friends list from Roblox's web API with httpget and refresh it periodically.
local friendIds = {}          -- [userId number] = true
local friendsLoaded = false
local lastFriendFetch = -999
local warnedFriendApi = false

local function fetchFriends()
    local myId = nil
    pcall(function() myId = plr.UserId end)
    if not myId or myId <= 0 then return false, "no UserId" end

    local ok, body = pcall(function()
        return httpget("https://friends.roblox.com/v1/users/" .. tostring(myId) .. "/friends")
    end)
    if not ok or type(body) ~= "string" or body == "" then
        return false, "request failed: " .. tostring(body)
    end

    local ids, count = {}, 0
    for id in string.gmatch(body, '"id"%s*:%s*(%d+)') do
        ids[tonumber(id)] = true
        count = count + 1
    end
    if count == 0 and not string.find(body, '"data"', 1, true) then
        return false, "unexpected response: " .. string.sub(body, 1, 60)
    end

    friendIds = ids
    return true, count
end

local function refreshFriends()
    -- retry every 10s until loaded once, then refresh every 60s
    local interval = friendsLoaded and 60 or 10
    if tick() - lastFriendFetch < interval then return end
    lastFriendFetch = tick()

    local ok, info = fetchFriends()
    if ok then
        if not friendsLoaded then
            friendsLoaded = true
            notify("Loaded " .. tostring(info) .. " friends. Friend Stop is active.", "Coin Farm", 4)
        end
    elseif not warnedFriendApi then
        warnedFriendApi = true
        warn("[CoinFarm] Friend list fetch failed: " .. tostring(info))
        notify("Friend list fetch failed (see console). Using FRIEND_NAMES only.", "Coin Farm", 6)
    end
end

local function isFriend(p)
    local lname = string.lower(p.Name)
    for _, n in ipairs(FRIEND_NAMES) do
        if string.lower(n) == lname then return true end
    end

    local id = nil
    pcall(function() id = p.UserId end)
    return id ~= nil and friendIds[id] == true
end

-- On-screen banner (big, top-center, stays up for BANNER_TIME seconds)
local BANNER_TIME = 10
local BANNER_W, BANNER_H = 340, 70
local bannerUntil = 0

local function mkBanner(kind, props, z)
    local d = Drawing.new(kind)
    for k, v in pairs(props) do pcall(function() d[k] = v end) end
    pcall(function() d.ZIndex = z end)
    d.Visible = false
    return d
end

local bnShadow = mkBanner("Square", { Filled = true, Color = C_SHADOW, Transparency = 0.35, Size = Vector2.new(BANNER_W, BANNER_H), Corner = 12 }, 30)
local bnBg     = mkBanner("Square", { Filled = true, Color = C_BG, Transparency = 1, Size = Vector2.new(BANNER_W, BANNER_H), Corner = 12 }, 31)
local bnBar    = mkBanner("Square", { Filled = true, Color = C_OFF, Transparency = 1, Size = Vector2.new(BANNER_W - 24, 3) }, 32)
local bnTitle  = mkBanner("Text", { Text = "", Color = C_TEXT, Outline = false, Center = true }, 33)
local bnSub    = mkBanner("Text", { Text = "", Color = C_DIM, Outline = false, Center = true }, 33)
pcall(function() bnTitle.FontSize = 18 end)
pcall(function() bnSub.FontSize = 14 end)

local function getScreenW()
    local w = 960
    pcall(function()
        local vs = workspace.CurrentCamera.ViewportSize
        if vs and vs.X and vs.X > 0 then w = vs.X end
    end)
    return w
end

local function showBanner(title, sub)
    bannerUntil = tick() + BANNER_TIME
    pcall(function() bnTitle.Text = title end)
    pcall(function() bnSub.Text = sub end)
end

task.spawn(function()
    local shown = false
    while true do
        local on = tick() < bannerUntil
        if on then
            local x = math.floor(getScreenW() / 2 - BANNER_W / 2)
            local y = 30
            pcall(function()
                bnShadow.Position = Vector2.new(x + 3, y + 4)
                bnBg.Position = Vector2.new(x, y)
                bnBar.Position = Vector2.new(x + 12, y + 8)
                bnTitle.Position = Vector2.new(x + BANNER_W / 2, y + 18)
                bnSub.Position = Vector2.new(x + BANNER_W / 2, y + 44)
            end)
        end
        if on ~= shown then
            shown = on
            bnShadow.Visible, bnBg.Visible, bnBar.Visible = on, on, on
            bnTitle.Visible, bnSub.Visible = on, on
        end
        wait(0.1)
    end
end)

local function friendStopTrigger(name)
    cfg.enabled = false
    status = "Stopped: friend joined"
    evt("friend: " .. tostring(name))
    showBanner("FRIEND JOINED: " .. tostring(name), "Farm stopped. Re-enable manually (F2).")
    notify(tostring(name) .. " joined. Farm stopped, re-enable manually.", "Coin Farm", 6)
end

task.spawn(function()
    local friendsHere = {}
    local firstScan = true
    local wasLoaded = false
    while true do
        local ok, err = pcall(function()
            refreshFriends()
            -- the moment the friends list first loads, friends already in the server
            -- become the baseline instead of counting as "just joined"
            if friendsLoaded and not wasLoaded then
                wasLoaded = true
                firstScan = true
            end
            local present = {}
            for _, p in ipairs(Players:GetPlayers()) do
                if p ~= plr and isFriend(p) then
                    present[p.UserId] = true
                    local isNew = not friendsHere[p.UserId]
                    local counts = (not firstScan) or CHECK_EXISTING_FRIENDS
                    if isNew and counts and cfg.friendStop and cfg.enabled then
                        friendStopTrigger(p.Name)
                    end
                end
            end
            friendsHere = present
            firstScan = false
        end)
        if not ok then warn("[CoinFarm friend] " .. tostring(err)) end
        wait(1)
    end
end)
 
notify("Coin farm loaded. F1 hides/shows the menu.", "Coin Farm", 4)
