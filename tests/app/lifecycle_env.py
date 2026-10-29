"""Only skip the real TCP restart check when the OS denies a listener."""
import errno
import os
import socket


def network_env():
    env = dict(os.environ)
    env.pop("LQ_TEST_NO_TCP", None)
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
    except OSError as error:
        if error.errno not in (errno.EPERM, errno.EACCES):
            raise
        env["LQ_TEST_NO_TCP"] = "1"
    return env
