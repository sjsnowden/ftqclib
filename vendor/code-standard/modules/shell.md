# Module — shell

What the standard's requirements mean in shell. A script is shell only while its whole job is to start programs and wait
for them (10.9).

- POSIX `sh`, not bash: no arrays, no `[[ ]]`, no process substitution. If it needs those it has outgrown shell.
- `set -eu` at the top, with what each letter buys.
- Quote every expansion. Build a long command as the positional arguments with `set --` and run it as `"$@"`, never as a
  string expanded unquoted.
- 8.6: every wait has a deadline: a counter in the loop, and an exit status and a message when it runs out.
- 8.4: `trap … EXIT` for anything that must not outlive the script.
- Say at the top why it is shell, so the next reader does not convert it out of habit.
- `shellcheck -s sh` clean.

<!-- brief: Shell -->
POSIX `sh`, `set -eu`, every expansion quoted, a counted deadline on every wait, `trap … EXIT`, `shellcheck -s sh`
clean.
<!-- /brief -->
