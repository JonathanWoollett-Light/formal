# Working on `index.html`

The website is one hand-written static file with no build step. Its design
system, the parts the test suite writes into it, and the syntax highlighter
are described in [DEVELOPMENT.md §6.3](DEVELOPMENT.md#63-the-website-indexhtml).

After any edit, run these in order (prettier first: it normalises the line
endings the metrics generator assumes):

```sh
npx prettier ./index.html --write
cargo run --example update_website   # must print "already in sync"
git diff --exit-code index.html
```
