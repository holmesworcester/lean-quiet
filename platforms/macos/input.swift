// External OS input for the native suite, never linked into the application.
import CoreGraphics
import Foundation
let args = CommandLine.arguments
precondition(CGPreflightPostEventAccess(), "Grant Accessibility input to the native test runner")
let scrolling = args[1] == "scroll" || args[1] == "scroll-click"
let start = scrolling ? 2 : 1
let p = CGPoint(x: Double(args[start])!, y: Double(args[start+1])!)
CGEvent(mouseEventSource: nil, mouseType: .mouseMoved, mouseCursorPosition: p, mouseButton: .left)!.post(tap: .cghidEventTap)
if scrolling {
    for i in 0..<Int(args[4])! {
        let event = CGEvent(scrollWheelEvent2Source: nil, units: .pixel, wheelCount: 1, wheel1: 24, wheel2: 0, wheel3: 0)!
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
