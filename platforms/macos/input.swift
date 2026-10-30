// External OS input for the native suite, never linked into the application.
import CoreGraphics
import Foundation
let args = CommandLine.arguments
precondition(CGPreflightPostEventAccess(), "Grant Accessibility input to the native test runner")
let p = CGPoint(x: Double(args[1])!, y: Double(args[2])!)
for type in [CGEventType.mouseMoved, .leftMouseDown, .leftMouseUp] {
    CGEvent(mouseEventSource: nil, mouseType: type, mouseCursorPosition: p, mouseButton: .left)!.post(tap: .cghidEventTap)
    usleep(60000)
}
