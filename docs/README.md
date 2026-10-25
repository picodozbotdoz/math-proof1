# `docs/` — the GitHub Pages root

This directory is served by GitHub Pages (branch `master`, folder `/docs`)
at **https://picodozbotdoz.github.io/math-proof1/** — it is the public front
door of the MathProof project. It contains no build step and makes no
network requests.

- **`index.html`** — the project landing page: headline results (Lehmer
  nonvanishing to n ≤ 65536, Ramanujan's congruence mod 691, the analytic
  bridge, small-modulus congruences), the 21 kernel-verified τ values, and
  how the kernel-only verification standard works. Single self-contained
  file (inline CSS, no JavaScript, no CDN).
- **`langlands.html`** — the standalone interactive educational page
  "The Langlands program, by example (GL₂)" (~44 KB): all CSS, JavaScript,
  and mathematics (newform coefficients, L-function, j-invariant) computed
  in the browser at load time; no cookies, analytics, or external calls.
- **`.nojekyll`** — tells Pages to serve the files verbatim instead of
  running Jekyll.

The τ values on the landing page must stay in sync with the theorems in
`MathProof/Tau/Basic.lean` (`tau_one` … `tau_twenty_one`) — update both
together.

## Quick preview locally

```bash
cd docs
python3 -m http.server 8000
# open http://localhost:8000
```

Because both pages are self-contained, any static file server or host
(nginx, Caddy, Cloudflare Pages, Netlify, S3) can serve this folder as-is.
