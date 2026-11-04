# One bounded Meta background research job

[background_meta.py](background_meta.py) is a separate client for one explicitly authorized public-mathematics prompt. It sends a fixed `muse-wonder-1.0` Responses request with `reasoning.effort="max"`, `max_output_tokens=65536`, and `background=true`. No model fallback, tools, files, prior response ID, encrypted reasoning, or model-generated code is used. Model output remains `UNVERIFIED`.

Meta documents background creation, retrieval by the returned ID, and cancellation. Cancellation can return a completed response when completion wins the race. Wonder's Responses MAX mode is documented separately. Sources: [Responses protocol](https://dev.meta.ai/docs/protocols/responses), [cancel endpoint](https://dev.meta.ai/docs/api-reference/responses/cancel-response), [Wonder MAX reasoning](https://dev.meta.ai/docs/reasoning#max-reasoning-on-muse-wonder).

## Invocation and ownership

The Python API is:

```python
from frontier.background_meta import run_background

# Within the user-authorized public-mathematics research scope:
state = run_background(public_math_prompt,
                       output_dir="frontier/background-meta-approved-job",
                       max_job_seconds=3600)

# Resume only that directory's already accepted ID; never start another request:
state = run_background(output_dir="frontier/background-meta-approved-job")
```

The CLI reads a new prompt only from explicit UTF-8 standard input:

```powershell
.venv\Scripts\python.exe -B frontier\background_meta.py --prompt-stdin --output frontier\background-meta-approved-job
```

Omit `--prompt-stdin` to resume the same directory. The client itself has no prompt-file, source attachment, arbitrary URL, response-ID, response-listing, or previous-response argument. It accepts only its persisted creation receipt. Merely importing the module does not read credentials or send requests.

An exclusive `session.lock` prevents concurrent operation in one result directory. `state.json` is atomically replaced after flushing and syncing. `accepted.json` is created exclusively, never overwritten, and binds the server-issued `resp_...` ID to this local job and its ledger reservation. The reservation and submission marker are durable before creation; the accepted ID is durable before parsing optional output or polling. Every poll/cancel reply must repeat the same owned ID. An ID mismatch stops with `PROTOCOL_UNCERTAIN`; it is never queried or cancelled.

If a process stops after an uncertain creation or cancellation request, restarting cannot automatically repeat that POST. Cancellation intent is durably marked `CANCELLATION_UNCERTAIN` before transport. Legacy saved `ACTIVE`/accepted states with a cancellation-request flag are also treated as uncertain on resume, without any network request or credential lookup. `SUBMISSION_UNCERTAIN` requires manual review. An accepted ID recovered from the receipt is retained; if its initial response was not parsed, the client attempts cancellation of that ID. Stale locks are not stolen or automatically deleted. Never remove a lock or change state while its recorded process may still be running.

## Spending reservation

The client opens **only the existing** project `logs/spending.json` ledger. Its `BudgetLedger` subclass omits automatic creation and checks the Meta cap inside the same ledger lock used by reservation and settlement. Missing/corrupt ledgers, a Meta cap above $125, or insufficient remaining allowance stop before creation. Existing caps, holds, and reservations are not reset.

Before the single POST, the client reserves the conservative full-context amount:

```
(1,048,576 input tokens * $4 + 65,536 output tokens * $20) / 1,000,000
= $5.505024
```

Only a terminal response for the owned ID can settle that reservation. Valid exact nonnegative input/output counts are priced at those same rates, including when the remote response is incomplete, failed, cancelled, or contains no visible answer. Invalid/missing/inconsistent usage leaves the full reservation pending. Intermediate queued/in-progress usage is never settled. Settlement and local-state recovery are idempotent only for the same measured amount. Actual overruns are recorded by the shared ledger and stop the client; they are not silently clamped or refunded.

This ledger coordinates cooperating project clients; it cannot cap unrelated account activity or guarantee a provider's final invoice. Prior pending reservations remain untouched.

## Deadline, request bounds, and cancellation

The immutable UTC deadline for this authorized session is **2026-11-04 19:42:17 UTC**. A job is additionally bounded by at most 3,600 seconds from its original start. Resuming preserves the earlier saved deadline and request count. Wall-clock and monotonic remaining-time checks prevent an in-process clock rollback from extending the job.

The client starts cancellation with a 15-second margin, leaving room before the final ten-second window. Poll waits are at most 15 seconds and are capped at this trigger. At most 250 HTTP operations are allowed, including creation and a reserved cancellation slot. Every HTTP operation has a total local wait of at most 30 seconds, shortened to the remaining deadline; ordinary POST/polls also preserve the cancellation margin. A daemon-thread boundary limits the wait even if urllib is stuck on DNS or a slowly trickling body. Redirects are rejected, and only the fixed HTTPS host and three fixed operation shapes are reachable.

Creating a file named `STOP` in this job directory requests cancellation between operations. STOP and remaining time are checked again immediately before transport. There is no new creation request after an uncertain POST, no response search, and no access to unrelated stored responses.

**Remote cancellation cannot be guaranteed if the network fails.** A timed-out creation may still have reached the provider; without a confirmed owned ID there is no safe cancellation target. A timed-out daemon operation can finish later, but its result is discarded and it starts no further requests. A failed, malformed, nonterminal, or unconfirmed cancellation leaves `CANCELLATION_UNCERTAIN`, `finished=false`, and a pending reservation. A successful cancellation race that returns `completed` is treated as an observed terminal result and its valid usage is settled. The client never labels an unconfirmed job finished.

## Saved information and result meaning

Saved state contains the prompt's SHA-256 hash, local job/owned response/reservation IDs, lifecycle fields, counters, deadlines, sanitized token usage, and visible final text. It does not save the prompt itself, request headers, credentials, response bodies, error bodies, reasoning summaries, or encrypted/hidden reasoning. Only completed assistant-message `output_text` blocks with absent phase or `phase="final_answer"` are retained; commentary and analysis phases are excluded. Any exact occurrence of the loaded API key in visible output is replaced with `[REDACTED]` before persistence.

`finished=true` means the provider reported one of `completed`, `incomplete`, `failed`, or `cancelled`; it does not mean a mathematical problem was solved. `incomplete=true` also covers completed responses with no visible final text. `claim_status` always remains `UNVERIFIED`. Resource/accounting/transport uncertainty is preserved rather than converted into success.

## Offline validation

[Tests](../tests/test_background_meta.py) use temporary ledgers inside the project, dummy credentials, injected clocks, and mocked transports. They cover reserve-before-POST, all lifecycle statuses, unknown usage, exact-key redaction, hidden-reasoning exclusion, ownership/receipt tampering, uncertain POST restart, settlement crash recovery, STOP, deadline cancellation, completion/cancellation races, request caps, redirect rejection, and bounded network waits.

```powershell
.venv\Scripts\python.exe -B -m unittest tests.test_background_meta -v
```

Twenty-one tests passed after cancellation-crash and strict saved-metadata regressions were added. No live request, real credential read, or mutation of the project's real spending ledger was performed in those checks. One authorized public-math job subsequently completed with visible output and recorded cost $0.74812; its independent regular Claude critique also completed. No request starts on import, and resuming a completed job does not create another one.
