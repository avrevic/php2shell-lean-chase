/-!
PHP2Shell, session upload-progress (CVE-2026-109618), smallest model, in Lean 4.

This project CHASES the bug: it states the property the bug breaks (`psIdLive`) and tries to
prove it after every way a request can end.

The PHP feature, and only it:
1. `MULTIPART_EVENT_FILE_START`: during multipart parse, before normal request init, the
   session id is allocated on the request heap and published in the worker global `PS(id)`.
2. Normal end: `php_rshutdown_session_globals` clears `PS(id)`, then the heap is destroyed.
3. Fatal out-of-memory: `zend_bailout` (a longjmp) skips step 2's clear; the heap is destroyed
   anyway, and `PS(id)` keeps pointing into it.
4. The next request on the same worker reaches upload-progress cleanup, trusts `PS(id)`
   (pointer + length) and copies those bytes into the `PHPSESSID` cookie.

The request heap carries a generation that ends with the request. A pointer is live only if
it was made in the current generation. This is the one thing C does not track.
-/

namespace Php2Shell

/-- The request heap: PHP's per-request `emalloc` arena. Everything a request allocates dies
together when it ends. `generation` names which request owns the heap. C has no such
field; adding it is what lets the spec say "this pointer belongs to a request that is over". -/
structure RequestHeap where
  bytes : List UInt8
  generation : Nat

/-- The value of `PS(id)`: in PHP a `zend_string *`, here an offset and a length into the
request heap, plus the generation of the request that allocated it. -/
structure SessionId where
  off : Nat
  len : Nat
  generation : Nat

/-- One PHP worker process. It serves many requests in turn and its globals outlive all of them.
`psId` stands for `PS(id)`, the session module's current session id. -/
structure Worker where
  psId : Option SessionId

/-- THE PROPERTY. A published `PS(id)` points to bytes the current request heap still owns:
same generation, and inside the heap. It is the general rule "a long-lived global must not
point into short-lived memory", and the only definition written with the bug in mind.
Every `*_live` theorem below asks whether a request end re-establishes it. -/
def psIdLive (w : Worker) (h : RequestHeap) : Prop :=
  match w.psId with
  | some id => id.generation = h.generation ∧ id.off + id.len ≤ h.bytes.length
  | none => True

/-- End of a request (`shutdown_memory_manager` in PHP): all allocations die and the next
request starts a new generation. -/
def RequestHeap.destroy (h : RequestHeap) : RequestHeap :=
  { bytes := [], generation := h.generation + 1 }

/-- PHP: the session upload-progress handler (`ext/session/session.c`, RFC 1867 callback) on
`MULTIPART_EVENT_FILE_START`, before normal request init. It allocates the session id on
the request heap and stores it in `PS(id)`. -/
def publishSessionId (_w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  ({ psId := some ⟨h.bytes.length, 1, h.generation⟩ }, { h with bytes := h.bytes ++ [sid] })

/-- PHP: `php_rshutdown_session_globals`, which clears `PS(id)`. The call the bug skips. -/
def rshutdownSessionGlobals (_w : Worker) : Worker :=
  { psId := none }

/-- PHP: `MULTIPART_EVENT_END`, the normal end: clear `PS(id)` first, then free the heap. -/
def requestEndNormal (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (rshutdownSessionGlobals w, h.destroy)

/-- THE BUG (CVE-2026-109618). Out of memory in the upload window: `zend_bailout` (a `longjmp`)
skips `php_rshutdown_session_globals`, the heap is freed anyway, and `PS(id)` keeps
pointing into a dead generation. See `requestEndFatalOom_live` (cannot be proved) and
`requestEndFatalOom_breaks_live` (its negation, proved). -/
def requestEndFatalOom (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (w, h.destroy)

/-- The same out-of-memory edge with the fix: clear the worker globals before freeing the heap. -/
def requestEndFatalOomFixed (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (rshutdownSessionGlobals w, h.destroy)

/-- PHP: the next request's upload-progress cleanup trusts `PS(id)`'s pointer and length and
URL-encodes those bytes into the `PHPSESSID` cookie. After the bug those bytes belong to
another request: the memory disclosure. `List.drop`/`List.take` are total, so the read
itself can never fail; only `psIdLive` says whether it reads the right request's bytes. -/
def uploadProgressCleanup (w : Worker) (h : RequestHeap) : List UInt8 :=
  match w.psId with
  | some id => (h.bytes.drop id.off).take id.len
  | none => []

/-- Right after publishing, `PS(id)` is live. Proved. -/
theorem publishSessionId_live (w : Worker) (h : RequestHeap) (sid : UInt8) :
    psIdLive (publishSessionId w h sid).1 (publishSessionId w h sid).2 := by
  simp [psIdLive, publishSessionId]

/-- The normal end re-establishes `psIdLive` (`PS(id)` is cleared). Proved. -/
theorem requestEndNormal_live (w : Worker) (h : RequestHeap) (sid : UInt8) :
    psIdLive (requestEndNormal w h sid).1 (requestEndNormal w h sid).2 := by
  simp [psIdLive, requestEndNormal, rshutdownSessionGlobals]

/-- The fixed fatal edge re-establishes `psIdLive`. Proved. So the property is not simply
unprovable on every fatal path: it fails only where the cleanup is skipped. -/
theorem requestEndFatalOomFixed_live (w : Worker) (h : RequestHeap) (sid : UInt8) :
    psIdLive (requestEndFatalOomFixed w h sid).1 (requestEndFatalOomFixed w h sid).2 := by
  simp [psIdLive, requestEndFatalOomFixed, rshutdownSessionGlobals]

/-- The obligation on the bug edge, stated like the others. It cannot be proved, because it is
false: `requestEndFatalOom_breaks_live` proves the opposite for every input. Lean has no
"failed" status (a false proof does not build), so the obligation stays `sorry` and
VeriLib shows it unverified. This `sorry` is the finding, not unfinished work. -/
theorem requestEndFatalOom_live (w : Worker) (h : RequestHeap) (sid : UInt8) :
    psIdLive (requestEndFatalOom w h sid).1 (requestEndFatalOom w h sid).2 := by
  sorry

/-- The bug, proved: after a fatal out-of-memory end, for every worker, heap and session id,
`PS(id)` points into a dead generation. This is the counterexample that explains why
`requestEndFatalOom_live` cannot be proved. -/
theorem requestEndFatalOom_breaks_live (w : Worker) (h : RequestHeap) (sid : UInt8) :
    ¬ psIdLive (requestEndFatalOom w h sid).1 (requestEndFatalOom w h sid).2 := by
  simp [psIdLive, requestEndFatalOom, publishSessionId, RequestHeap.destroy]

/-- Given `psIdLive`, the cookie has exactly the published length and comes from this request's
own heap. Proved. The precondition is what every request end must hand over. -/
theorem uploadProgressCleanup_in_bounds (w : Worker) (h : RequestHeap) (hl : psIdLive w h) :
    (uploadProgressCleanup w h).length = (match w.psId with | some id => id.len | none => 0) := by
  unfold psIdLive at hl
  unfold uploadProgressCleanup
  split <;> simp_all
  omega

end Php2Shell
