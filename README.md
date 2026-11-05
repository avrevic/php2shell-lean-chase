# php2shell-lean-chase

The smallest model of one [PHP2Shell](https://www.wiz.io/blog/php2shell-php-rce) bug (CVE-2026-109618, session upload-progress memory disclosure), in Lean 4. This version **chases the bug**: it states `psIdLive` ("a published `PS(id)` points to bytes the current request heap still owns") and tries to prove it after every way a request can end. The heap carries a generation that ends with the request. C has no such tag.

Same model without that property: [php2shell-lean-plain](https://github.com/avrevic/php2shell-lean-plain). Verus versions: [php2shell-chase](https://github.com/avrevic/php2shell-chase), [php2shell-plain](https://github.com/avrevic/php2shell-plain).

| Theorem | Status |
|---|---|
| `publishSessionId_live` | proved |
| `requestEndNormal_live` | proved |
| `requestEndFatalOomFixed_live` (fix: clear globals first) | proved |
| `requestEndFatalOom_live` (**the bug**) | **`sorry`: cannot be proved** |
| `requestEndFatalOom_breaks_live`: its negation, for every input | proved |
| `uploadProgressCleanup_in_bounds`, given `psIdLive` | proved |

Lean has no "failed" status: a false theorem does not build. Finding the bug here looks like this: the property cannot be proved on exactly one edge, and its negation can. **With the property written down, the flaw is found.**

```sh
lake build                 # one warning: declaration uses `sorry`
probe-lean extract .       # VeriLib probe output in .verilib/probes/
```
