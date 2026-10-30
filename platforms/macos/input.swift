// External OS input for the native suite, never linked into the application.
import CoreGraphics
import Foundation
import AppKit
import ApplicationServices
let args = CommandLine.arguments
precondition(CGPreflightPostEventAccess(), "Grant Accessibility input to the native test runner")
if args[1] == "ready" {
    let front=NSWorkspace.shared.frontmostApplication
    if front?.bundleIdentifier == "com.apple.loginwindow" || front?.localizedName == "loginwindow" {
        fputs("Unlock the Mac desktop before running native input tests.\n",stderr)
        exit(2)
    }
    exit(0)
}
if ["window", "key", "text"].contains(args[1]) {
    let pid=pid_t(args[2])!
    NSRunningApplication(processIdentifier:pid)?.activate(options:[])
    let target=AXUIElementCreateApplication(pid)
    precondition(AXUIElementSetAttributeValue(target,kAXFrontmostAttribute as CFString,kCFBooleanTrue) == .success)
    // Wait for the WindowServer activation/Stage Manager transform to finish.
    // During it, visible window bounds can be scaled to 90% of their size.
    usleep(600000)
    if args[1] == "window" {
        if args.count == 5 {
            let app=AXUIElementCreateApplication(pid)
            var value:CFTypeRef?
            precondition(AXUIElementCopyAttributeValue(app,kAXWindowsAttribute as CFString,&value) == .success)
            let windows=value as! [AXUIElement]
            precondition(!windows.isEmpty,"No accessible app window")
            var size=CGSize(width:Double(args[3])!,height:Double(args[4])!)
            precondition(AXUIElementSetAttributeValue(windows[0],kAXSizeAttribute as CFString,AXValueCreate(.cgSize,&size)!) == .success)
            usleep(100000)
        }
        // WindowServer geometry is independent of the renderer and text view.
        // It also avoids stale AXPosition proxies during app startup.
        var rect:CGRect?
        for _ in 0..<50 {
            let windows=CGWindowListCopyWindowInfo([.optionOnScreenOnly,.excludeDesktopElements],kCGNullWindowID) as! [[String:Any]]
            if let win=windows.first(where:{ ($0[kCGWindowOwnerPID as String] as? Int)==Int(pid) && ($0[kCGWindowLayer as String] as? Int)==0 }),
               let bounds=win[kCGWindowBounds as String] as? [String:Any] {
                rect=CGRect(dictionaryRepresentation:bounds as CFDictionary)
                break
            }
            usleep(100000)
        }
        guard let rect=rect else { fatalError("No WindowServer window for test app") }
        print("\(Int(rect.origin.x)) \(Int(rect.origin.y)) \(Int(rect.width)) \(Int(rect.height))")
    } else {
        usleep(100000)
        let code=args[1] == "key" ? CGKeyCode(args[3])! : 0
        for down in [true,false] {
            let event=CGEvent(keyboardEventSource:nil,virtualKey:code,keyDown:down)!
            if args[1] == "text" {
                let chars=Array(args[3].utf16)
                chars.withUnsafeBufferPointer { event.keyboardSetUnicodeString(stringLength:$0.count,unicodeString:$0.baseAddress!) }
            } else if args.count>4 { event.flags = .maskCommand }
            event.postToPid(pid)
            usleep(60000)
        }
    }
    exit(0)
}

let resizing = args[1] == "resize"
let scrolling = args[1] == "scroll" || args[1] == "scroll-click"
let start = scrolling || resizing ? 2 : 1
let p = CGPoint(x: Double(args[start])!, y: Double(args[start+1])!)
CGEvent(mouseEventSource: nil, mouseType: .mouseMoved, mouseCursorPosition: p, mouseButton: .left)!.post(tap: .cghidEventTap)
if resizing {
    CGEvent(mouseEventSource:nil,mouseType:.leftMouseDown,mouseCursorPosition:p,mouseButton:.left)!.post(tap:.cghidEventTap)
    for i in 1...60 {
        let q = CGPoint(x:p.x + Double(args[4])! * Double(i)/60,
                        y:p.y + Double(args[5])! * Double(i)/60)
        CGEvent(mouseEventSource:nil,mouseType:.leftMouseDragged,mouseCursorPosition:q,mouseButton:.left)!.post(tap:.cghidEventTap)
        usleep(40000)
    }
    usleep(800000)
    let q = CGPoint(x:p.x + Double(args[4])!, y:p.y + Double(args[5])!)
    CGEvent(mouseEventSource:nil,mouseType:.leftMouseUp,mouseCursorPosition:q,mouseButton:.left)!.post(tap:.cghidEventTap)
} else if scrolling {
    let count=Int(args[4])!
    for i in 0..<abs(count) {
        let event = CGEvent(scrollWheelEvent2Source: nil, units: .pixel, wheelCount: 1, wheel1: count<0 ? -24 : 24, wheel2: 0, wheel3: 0)!
        event.location=p
        event.setIntegerValueField(.scrollWheelEventIsContinuous, value: 1)
        event.post(tap: .cghidEventTap)
        usleep(16000)
        if args[1] == "scroll-click" && i == 5 {
            CGEvent(mouseEventSource:nil,mouseType:.leftMouseDown,mouseCursorPosition:p,mouseButton:.left)!.post(tap:.cghidEventTap)
            usleep(30000)
            CGEvent(mouseEventSource:nil,mouseType:.leftMouseUp,mouseCursorPosition:p,mouseButton:.left)!.post(tap:.cghidEventTap)
        }
    }
} else {
    for type in [CGEventType.leftMouseDown, .leftMouseUp] {
        CGEvent(mouseEventSource: nil, mouseType: type, mouseCursorPosition: p, mouseButton: .left)!.post(tap: .cghidEventTap)
        usleep(60000)
    }
}
