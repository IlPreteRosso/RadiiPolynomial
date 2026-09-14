# Optional trigger lines (user-applied; the package never edits instruction files)

Paste ONE line into the global instruction file of each harness so a fresh session in any
project knows to look for the bus when another agent session is around. The line invokes the
skill; it does not create activation, arm a scheduler, or grant any permission.

Claude Code — `~/.claude/CLAUDE.md`:
```
- If another agent session works on the same checkout, load and follow the `agents-bus` skill (its SKILL.md) before touching shared files or registering anywhere; it tells you how to find or join the bus that is actually in use.
```

Codex — its global `AGENTS.md`:
```
- If another agent session works on the same checkout, load and follow the `agents-bus` skill from your skills directory (its SKILL.md) before touching shared files or registering anywhere; it tells you how to find or join the bus that is actually in use.
```

Keeping bus artifacts untracked: `init` prints the ignore line for the bus directory and never
applies it; add it (and, if you prefer, the `.agents_bus` marker) to the project's `.gitignore`
yourself.
