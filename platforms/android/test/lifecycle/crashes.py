"""Attribute Android threadtime crash lines to the actual target process."""
import re

MARKERS=('Fatal signal','FATAL EXCEPTION','FORTIFY:','JNI DETECTED ERROR','PANIC','uncaught exception')

def crash_lines(transcript,pid):
    target=[];external=[]
    for line in transcript.splitlines():
        if not any(marker in line for marker in MARKERS):continue
        match=re.match(r'^\S+\s+\S+\s+(\d+)\s+\d+\s+[VDIWEF]\s',line)
        # An unparseable crash line must never silently pass as unrelated.
        (target if match is None or match.group(1)==pid else external).append(line)
    return target,external
