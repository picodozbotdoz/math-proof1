# The Langlands program, by example (GL₂) — deployable page

`index.html` is a **single self-contained file** (~44 KB): all CSS, JavaScript, and
mathematics (newform coefficients, L-function, j-invariant) are computed in the
browser at load time. It makes **no network requests** — no CDN, fonts, or data
files — so any static file server can host it.

## Quick preview locally

```bash
cd langlands-site
python3 -m http.server 8000
# open http://localhost:8000
```

## Deployment options

**nginx** — drop the folder into the web root:

```nginx
server {
    listen 80;
    server_name example.com;
    root /var/www/langlands-site;
    index index.html;
}
```

**Caddy** — one line, automatic HTTPS:

```
example.com {
    root * /var/www/langlands-site
    file_server
}
```

**Docker + nginx:**

```dockerfile
FROM nginx:alpine
COPY index.html /usr/share/nginx/html/index.html
EXPOSE 80
```

`docker build -t langlands-page . && docker run -p 8080:80 langlands-page`

**Static hosts** — GitHub Pages, Cloudflare Pages, Netlify, S3 + CloudFront:
upload `index.html` as the site root; no build step needed.

## Notes

- Light/dark theme follows the visitor's `prefers-color-scheme` automatically.
- No cookies, analytics, or external calls — safe to host anywhere, including
  air-gapped environments.
- Source of truth for the interactive fragment:
  `~/.zcode/v2/visualizations/06cf066f8579370a3f604fd97ad33f354220e454974d61d9d232dffdb80fa549/automorphic-forms-langlands.html`
