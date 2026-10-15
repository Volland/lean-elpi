# Publishing the bindings

LeanElpi ships to three registries from one version tag: **PyPI** (`pip install leanelpi`),
**npm** (`npm install @lean-elpi/leanelpi`) and **crates.io** (`cargo add leanelpi`). The release workflow
(`.github/workflows/release.yml`) builds the native library on four platforms, tests all three
bindings against it, and publishes. This file is the one-time setup and the release routine.

The names `leanelpi` (PyPI and crates.io) were unregistered when this was written. Check them
again before you start, because the first person to publish a name owns it. On npm the packages
live in the `@lean-elpi` organisation, which you own, so their names cannot be taken.

## 0. What gets published

| Registry | Artefact | Notes |
|---|---|---|
| PyPI | 4 wheels (Linux wheels also carry `libleanshared.so`) `leanelpi-X-py3-none-<platform>.whl`, about 44 MB each | one wheel per platform serves every Python 3 version; no source distribution |
| npm | `@lean-elpi/leanelpi` (loader, a few KB) and 4 packages `@lean-elpi/leanelpi-<os>-<cpu>` (about 44 MB each) | npm installs only the one matching the machine, through `optionalDependencies` |
| crates.io | `leanelpi` (26 KB) | the crate does not contain the native library; users download it from the GitHub release |
| GitHub release | `libleanelpi-<platform>.tar.gz` | the library and header, for Rust and C users |

## Quick setup of the GitHub side

`scripts/setup-github.sh` creates the environments `pypi`, `npm` and `crates` through the `gh` CLI.
Each requires your approval before a publish job runs and accepts only tags `v*`. Then store
the two secrets (PyPI needs none):

```bash
gh auth login                              # once; needs admin on the repository
scripts/setup-github.sh                    # environments
scripts/setup-github.sh secrets            # ...and prompts for the two tokens, hidden input
# or one by one, without the script:
gh secret set NPM_TOKEN --env npm --repo Volland/lean-elpi
gh secret set CARGO_REGISTRY_TOKEN --env crates --repo Volland/lean-elpi
gh secret list --env npm --repo Volland/lean-elpi        # names only; values are never shown
```

Two steps cannot be done from a CLI: creating the tokens (on npmjs.com and crates.io) and the
PyPI pending publisher (section 1.2). Everything else below is covered by the script.

## 1. PyPI

### 1.1 Account

1. Register at <https://pypi.org/account/register/> and verify the email address.
2. Turn on two-factor authentication (Account settings → Add 2FA). PyPI requires it to publish.
3. Do the same on <https://test.pypi.org> if you want a rehearsal (a separate account).

### 1.2 Trusted publishing (recommended: no token to store or leak)

The release job proves its identity to PyPI with a short-lived OpenID Connect token.

1. Open <https://pypi.org/manage/account/publishing/> → **Add a new pending publisher**.
2. Fill in:
   - PyPI project name: `leanelpi`
   - Owner: `Volland`, repository: `lean-elpi`
   - Workflow name: `release.yml`
   - Environment name: `pypi`
3. The GitHub environment `pypi` is created by `scripts/setup-github.sh`.

The first successful publish creates the project and turns the pending publisher into a normal one.

### 1.3 Rehearsal on TestPyPI (optional)

Repeat 1.2 on <https://test.pypi.org/manage/account/publishing/> with environment `testpypi`,
copy the `publish-pypi` job, and add `repository-url: https://test.pypi.org/legacy/` to the
action. Then install with
`pip install -i https://test.pypi.org/simple/ leanelpi`.

### 1.4 Fallback: upload by hand with an API token

Only wheels for the platform you build on exist locally, so this publishes one platform. Use it
for a first smoke test, not for a real release.

```bash
python -m venv .venv && . .venv/bin/activate
pip install build twine
scripts/package-python.sh                 # writes dist/wheels/*.whl and runs twine check
# Account settings → API tokens → Add API token (scope: the project, or "entire account" for the first upload)
twine upload dist/wheels/*.whl            # username: __token__   password: pypi-…
```

## 2. npm

1. Register at <https://www.npmjs.com/signup>, verify the email and enable 2FA
   (Account → Two-Factor Authentication, "Authorization and publishing").
2. The organisation `lean-elpi` (npmjs.com/org/lean-elpi) provides the scope `@lean-elpi`. Your
   account must be an owner or a member with write access. Public scoped packages are free.
3. Create an access token: Account → Access Tokens → **Generate New Token** → *Granular access
   token*, permission *Read and write*, limited to the `@lean-elpi` scope, and tick *Bypass
   two-factor authentication* only if you publish from CI (npm cannot ask for a code there).
   Set a short expiry.
4. Store it: `gh secret set NPM_TOKEN --env npm --repo Volland/lean-elpi` (the environment
   already exists).
5. Scoped packages are private by default. Every package here sets `publishConfig.access` to
   `public`, and the workflow passes `--access public`, so nothing extra is needed.

Publishing by hand: `npm login`, then for each tarball in `dist/npm/`:
`npm publish dist/npm/lean-elpi-leanelpi-darwin-arm64-0.3.1.tgz --access public`, platform packages first,
`npm publish dist/npm/lean-elpi-leanelpi-0.3.1.tgz --access public` last. Do not publish the loader before
the platform packages exist, or installs resolve a missing optional dependency.

## 3. crates.io

1. Log in at <https://crates.io> with GitHub, and verify your email (Account Settings → Email).
2. Account Settings → API Tokens → **New Token**; scopes `publish-new` and `publish-update`.
3. Store it: `gh secret set CARGO_REGISTRY_TOKEN --env crates --repo Volland/lean-elpi`.

By hand: `cargo login`, then
`cd bindings/rust && LEANELPI_DIST=$PWD/../../dist cargo publish --dry-run`, then without
`--dry-run`. The dry run compiles the packaged crate and links the library, so `dist/` must
hold a built `libleanelpi`.

## 4. Before the first release

```bash
scripts/check-versions.sh         # every binding carries the version in lakefile.lean
scripts/build-ffi.sh              # dist/libleanelpi.* (needs elan and a C compiler)
scripts/check-ffi-deps.sh         # depends on system libraries only
(cd bindings/python && python -m pytest)
(cd bindings/node && npm install && npm test)
(cd bindings/rust && cargo test)
scripts/package-python.sh && scripts/package-node.sh
```

Then push the branch and open **Actions → release → Run workflow**. It builds and tests on all
four platforms and publishes nothing, because publishing needs a tag. Fix whatever fails there.
The Linux and Intel macOS builds have never run before this step. Expect to adjust the
wheel's `manylinux` tag if `auditwheel show` (run it on the wheel) reports a newer glibc than
the tag claims.

## 5. A release

1. Choose the version `X.Y.Z`. Change it in `lakefile.lean`, `Elpi/Ffi.lean` (`version`),
   `bindings/python/pyproject.toml`, `bindings/rust/Cargo.toml`, `bindings/node/package.json`
   (including the four `optionalDependencies`). `scripts/check-versions.sh` checks all of them.
2. Move the `Unreleased` section of `CHANGELOG.md` under the new version.
3. Commit, then tag and push:
   ```bash
   git tag vX.Y.Z && git push origin main vX.Y.Z
   ```
4. Watch **Actions → release**. Approve the `pypi`, `npm` and `crates` environments when asked.
   The jobs run in this order: build (4 platforms) → PyPI, npm, crates.io → GitHub release.
5. Check from a clean directory:
   ```bash
   pip install leanelpi==X.Y.Z && python -c "import leanelpi; print(leanelpi.version())"
   npm install @lean-elpi/leanelpi@X.Y.Z && node -e "console.log(require('@lean-elpi/leanelpi').version())"
   ```

## 6. When something goes wrong

- **A registry rejects one platform halfway.** PyPI and npm versions are immutable. Fix the
  problem, bump the patch version, and release again. A partly published version can stay;
  yank it (`pip` users: PyPI → Manage → Yank; npm: `npm deprecate @lean-elpi/leanelpi@X.Y.Z "use X.Y.Z+1"`;
  crates.io: `cargo yank --version X.Y.Z`).
- **Wheel too large.** PyPI's default limit is 100 MB per file. Wheels are about 44 MB. If
  they grow, ask for a limit increase at <https://pypi.org/help/#file-size-limit>.
- **`pip install` picks no wheel on Linux.** The wheel's `manylinux_2_35` tag needs glibc 2.35
  or newer on the user's machine. Build on an older image for wider reach.
- **Windows.** Not supported. The engine builds with the Lean toolchain on Windows, but the
  build script, the shim's thread handling and the wheel tags have not been ported.
