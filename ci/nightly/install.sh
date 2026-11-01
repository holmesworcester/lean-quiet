#!/usr/bin/env bash
# Install the nightly forensics judge as a systemd user timer (03:30
# daily). The rates accumulate in /mnt/storage/holmes-tmp/forensics-nightly/history.tsv.
# Remove: systemctl --user disable --now lq-forensics-judge.timer
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p ~/.config/lq-nightly ~/.config/systemd/user
sed "s#^repo=.*#repo=$(git -C "$here" rev-parse --path-format=absolute --git-common-dir)#" "$here/run.sh" > ~/.config/lq-nightly/run.sh
cp "$here/lq-forensics-judge.service" "$here/lq-forensics-judge.timer" ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable --now lq-forensics-judge.timer
systemctl --user list-timers lq-forensics-judge.timer --no-pager
