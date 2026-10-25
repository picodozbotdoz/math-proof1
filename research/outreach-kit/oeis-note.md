# OEIS A000594 — a passive, discussion-free contribution

The OEIS entry for the Ramanujan τ function (A000594) is one of the places
number theorists actually look. One line there makes the verified values
permanently discoverable without any community interaction: the OEIS is
wiki-style — you submit an edit, moderators approve it, no discussion
involved.

## The line to add (LINKS section)

```
D. Zulkarnaen, <a href="https://github.com/picodozbotdoz/math-proof1">MathProof:
formally verified modular-forms mathematics in Lean 4</a> — the first 21 terms
are proved as individual <tt>decide</tt> theorems by Lean 4's kernel
(<tt>MathProof/Tau/Basic.lean</tt>), and τ(n) ≠ 0 is kernel-certified for all
n ≤ 65536 (<tt>MathProof/Tau/LehmerPacked.lean</tt>).
```

## How

1. Register at https://oeis.org (free) and sign in.
2. Open https://oeis.org/A000594 and click **edit** at the top of the page.
3. In the LINKS section, add the line above (keep the section's ordering
   convention if it is alphabetized by author).
4. Fill in the edit's "reason" field, e.g.: *Adding a link to a Lean 4
   formalization in which the first 21 terms and nonvanishing of τ up to
   n = 65536 are verified by Lean's kernel.*
5. **Preview**, then **submit**. Moderation typically takes a few days and
   needs no follow-up.

Keep the claim exactly as written — it states precisely what the repository
proves (21 decided values, nonvanishing to 65536) and nothing more, which is
what OEIS moderators expect from link contributions.
