// External OS input for the native suite, never linked into the application.
import CoreGraphics
import Foundation
import AppKit
import ApplicationServices
let args = CommandLine.arguments
precondition(CGPreflightPostEventAccess(), "Grant Accessibility input to the native test runner")
if ["window", "key", "text"].contains(args[1]) {
    let pid=pid_t(args[2])!
    NSRunningApplication(processIdentifier:pid)?.activate(options:[])
    let target=AXUIElementCreateApplication(pid)
    precondition(AXUIElementSetAttributeValue(target,kAXFrontmostAttribute as CFString,kCFBooleanTrue) == .success)
    if args[1] == "window" {
        let app=AXUIElementCreateApplication(pid)
        var value:CFTypeRef?
        precondition(AXUIElementCopyAttributeValue(app,kAXWindowsAttribute as CFString,&value) == .success)
        let windows=value as! [AXUIElement]
        precondition(!windows.isEmpty,"No accessible app window")
        let window=windows[0]
        AXUIElementSetMessagingTimeout(window,5)
        func read(_ attribute: String) -> CFTypeRef {
            var result:CFTypeRef?
            for _ in 0..<50 {
                if AXUIElementCopyAttributeValue(window,attribute as CFString,&result) == .success, let result=result { return result }
                usleep(100000)
            }
            fatalError("Window attribute unavailable: \(attribute)")
        }
        if args.count == 5 {
            var size=CGSize(width:Double(args[3])!,height:Double(args[4])!)
            precondition(AXUIElementSetAttributeValue(window,kAXSizeAttribute as CFString,AXValueCreate(.cgSize,&size)!) == .success)
        }
        value=read(kAXPositionAttribute)
        var point=CGPoint.zero; AXValueGetValue(value as! AXValue,.cgPoint,&point)
        value=read(kAXSizeAttribute)
        var size=CGSize.zero; AXValueGetValue(value as! AXValue,.cgSize,&size)
        print("\(Int(point.x)) \(Int(point.y)) \(Int(size.width)) \(Int(size.height))")
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
        if args.count>5 { event.postToPid(pid_t(args[5])!) }
        else { event.post(tap: .cghidEventTap) }
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
