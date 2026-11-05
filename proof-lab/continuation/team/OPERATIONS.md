# Local research team controls

Use the three command files in `C:\Users\email\muse-spark-chat`:

| File | Action |
|---|---|
| `START-RESEARCH.cmd` | Create one new reviewed queue and launch its controller hidden in the background. A duplicate or stopped/ambiguous previous run is refused. |
| `STATUS-RESEARCH.cmd` | Show the current run, roles, heartbeat, task phases, latest response summaries and local budget snapshot. |
| `STOP-RESEARCH.cmd` | Request a stop for **all** research-team runs and wait up to 85 seconds for confirmation. Local termination and remote cancellation are reported separately. |

Double-click a command file; its window stays open so the result can be read. From an existing terminal, add `--no-pause` to return without the final keypress. For example:

```powershell
.\STATUS-RESEARCH.cmd --no-pause
.\STOP-RESEARCH.cmd --no-pause
```

The start helper uses `Start-Process -WindowStyle Hidden`; closing this chat, Cursor, or the launcher window does not itself stop a started controller. The controller must confirm a fresh heartbeat before the helper reports successful startup. A missing heartbeat triggers a stop request for that new run; it never triggers an automatic retry. No execution-policy bypass, global settings, startup registration, or scheduled task is installed. If local script policy blocks execution, report that blocker rather than bypassing it.

## Workers and scope

The main research workers use **Muse Wonder MAX through the existing guarded Meta API client**. This is not the Muse Code CLI backend. The CLI has no verified per-run dollar ceiling here, so it is not used for unattended spending. The independent critics use **Claude Code with the existing subscription sign-in**, not the Claude API. Prompts contain only public mathematics and explicitly selected completed visible responses. No keys, `.env` content, private source files, or unrelated computer files are sent as model context. Model output is data, never an executable instruction channel.

The reviewed [queue](RESEARCH_QUEUE.md) has eight tasks: five Meta proposals and three Claude Code critiques. Initial independent work can overlap; dependent tasks wait for their named inputs. This is a finite research queue. Exhausting it produces `WAITING_FOR_REVIEW`, not a solution or an automatically invented new queue. Duplicate/no-progress/error and spending safeguards can also stop further requests. `SUCCEEDED` means a completed, structurally valid model response; **every mathematical claim remains UNVERIFIED** until independently checked. A full-solution claim requires human review.

Existing total project limits remain **$115 Meta** and **$40 Claude API**. These workers make no Claude API calls. Existing reservations and external holds remain intact. Status amounts come from the local project ledger, not verified provider account balances; unresolved charges are not silently refunded. Individual provider requests are bounded even though no arbitrary overall wall-clock deadline is imposed on the queue.

## Stopping and monitoring

`STOP-RESEARCH.cmd` is the independent local stop control. It prevents new team work and requests cancellation of owned calls. An active remote request may not stop instantly: read the receipt's confirmed and uncertain states separately. Unknown outcomes retain their financial reservations. The controller contains its own worker process trees; it does not kill unrelated computer processes.

Saying **stop** in this chat requires the assistant to receive the instruction and invoke the stop command. These workers do not monitor arbitrary chats, microphone input, or other applications. Use the local STOP command for a direct stop independent of this chat.

Keep the PC awake and connected for coordination, progress and cancellation. Sleep, shutdown or lost connectivity can delay confirmation of a remote request. There is no automatic startup after reboot. START does not resume an old run or delete STOP markers. A later restart after STOP or an ambiguous crash requires an explicit reviewed reset; do not delete the markers or locks casually.

## Local records

`proof-lab/continuation/team/CURRENT.json` identifies the current run. Runtime records and visible results are under `proof-lab/continuation/team/runs/<run-id>/`. The launcher writes `launcher.json`, `controller-stdout.log` and `controller-stderr.log` there. The controller owns `state.json`, heartbeats, task receipts and process ownership. Runtime files are excluded from Git by the team's local ignore rules.

For a read-only path check that launches no process or model request:

```powershell
powershell.exe -NoProfile -File .\proof-lab\continuation\team\Research-Team.ps1 -Action Validate
```

The helper's `-Action Start -Simulate` option is reserved for the setup/test workflow. It exercises local contained processes without provider calls; it is not live research. Simulation stop markers are still real local controls and must not be silently cleared before a live run.
