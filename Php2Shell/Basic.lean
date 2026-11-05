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

/-- The request heap (`emalloc` arena) and which request it belongs to. -/
structure RequestHeap where
  bytes : List UInt8
  generation : Nat

/-- `zend_string *` stored in `PS(id)`: where the bytes are, and which request made them. -/
structure SessionId where
  off : Nat
  len : Nat
  generation : Nat

/-- Process-lifetime globals of one PHP worker. `psId` is `PS(id)`. -/
structure Worker where
  psId : Option SessionId

/-- The spec: a published `PS(id)` points to bytes the current request heap still owns. -/
def psIdLive (w : Worker) (h : RequestHeap) : Prop :=
  match w.psId with
  | some id => id.generation = h.generation ∧ id.off + id.len ≤ h.bytes.length
  | none => True

/-- End of a request: every allocation dies; the next request starts a new generation. -/
def RequestHeap.destroy (h : RequestHeap) : RequestHeap :=
  { bytes := [], generation := h.generation + 1 }

/-- `MULTIPART_EVENT_FILE_START`: allocate the id on the request heap and publish it. -/
def publishSessionId (_w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  ({ psId := some ⟨h.bytes.length, 1, h.generation⟩ }, { h with bytes := h.bytes ++ [sid] })

/-- `php_rshutdown_session_globals`. -/
def rshutdownSessionGlobals (_w : Worker) : Worker :=
  { psId := none }

/-- `MULTIPART_EVENT_END`: clear the globals, then the heap dies. -/
def requestEndNormal (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (rshutdownSessionGlobals w, h.destroy)

/-- THE BUG. Out of memory: `zend_bailout` skips `php_rshutdown_session_globals`; the heap is
destroyed anyway. -/
def requestEndFatalOom (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (w, h.destroy)

/-- The same fatal edge with the fix: clear the worker globals before the heap is freed. -/
def requestEndFatalOomFixed (w : Worker) (h : RequestHeap) (sid : UInt8) : Worker × RequestHeap :=
  let (w, h) := publishSessionId w h sid
  (rshutdownSessionGlobals w, h.destroy)

/-- The next request: upload-progress cleanup copies `PS(id)` into the `PHPSESSID` cookie. -/
def uploadProgressCleanup (w : Worker) (h : RequestHeap) : List UInt8 :=
  match w.psId with
  | some id => (h.bytes.drop id.off).take id.len
  | none => []

theorem publishSessionId_live (w : Worker) (h : RequestHeap) (sid : UInt8) :
    psIdLive (publishSessionId w h sid).1 (publishSessionId w h sid).2 := by
  simp [psIdLive, publishSessionId]

theorem requestEndNormal_live (w : Worker) (h : RequestHeap) (sid : UInt8) :
    psIdLive (requestEndNormal w h sid).1 (requestEndNormal w h sid).2 := by
  simp [psIdLive, requestEndNormal, rshutdownSessionGlobals]

theorem requestEndFatalOomFixed_live (w : Worker) (h : RequestHeap) (sid : UInt8) :
    psIdLive (requestEndFatalOomFixed w h sid).1 (requestEndFatalOomFixed w h sid).2 := by
  simp [psIdLive, requestEndFatalOomFixed, rshutdownSessionGlobals]

/-- The obligation on the bug edge. It cannot be proved: its negation is proved below, for
every input. It stays `sorry`, so VeriLib shows it unverified. -/
theorem requestEndFatalOom_live (w : Worker) (h : RequestHeap) (sid : UInt8) :
    psIdLive (requestEndFatalOom w h sid).1 (requestEndFatalOom w h sid).2 := by
  sorry

/-- The bug, proved: after a fatal OOM, `PS(id)` always points into a dead generation. -/
theorem requestEndFatalOom_breaks_live (w : Worker) (h : RequestHeap) (sid : UInt8) :
    ¬ psIdLive (requestEndFatalOom w h sid).1 (requestEndFatalOom w h sid).2 := by
  simp [psIdLive, requestEndFatalOom, publishSessionId, RequestHeap.destroy]

/-- Given `psIdLive`, the cookie is made only of this request's own bytes. -/
theorem uploadProgressCleanup_in_bounds (w : Worker) (h : RequestHeap) (hl : psIdLive w h) :
    (uploadProgressCleanup w h).length = (match w.psId with | some id => id.len | none => 0) := by
  unfold psIdLive at hl
  unfold uploadProgressCleanup
  split <;> simp_all
  omega

end Php2Shell
