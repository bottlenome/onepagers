# INSTALL.md — Lean 4 環境構築手順（新セッション/新環境向け）

このプロジェクトのビルドに必要なのは **Lean 4 core v4.30.0（lean と lake の 2 バイナリ）だけ**である。
mathlib 等の外部依存は**ゼロ**（`lakefile.toml` 参照）なので、**ツールチェーンさえ入ればあとは完全オフラインでビルドできる**。

- 要求バージョン: `lean-toolchain` に固定 → `leanprover/lean4:v4.30.0`
- 対象アーキテクチャ: linux x86_64（それ以外は各方法の URL/asset 名を読み替え）

---

## 0. まず確認（インストール不要かもしれない）

```bash
which lean lake && lean --version
# "Lean (version 4.30.0, ...)" が出ればインストール不要。§4 の動作確認へ
ls /nix/store/ 2>/dev/null | grep lean4
# 何か出れば Nix 提供済み。例:
#   export PATH=/nix/store/<ハッシュ>-lean4-4.30.0/bin:$PATH
# （issue #48 §1.1 の /nix/store/9926168...-lean4-4.30.0 は元コンテナ固有のハッシュ。
#   自分の環境で ls した結果のパスに読み替えること）
```

---

## 1. 方法 A: elan（標準・第一候補）

[elan](https://github.com/leanprover/elan) は Lean のバージョンマネージャ。リポジトリの `lean-toolchain` を自動で読んで正しい版を使う。

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"     # または source $HOME/.elan/env
cd <リポジトリ>/iut-lean-verification
lake --version    # ← ここで elan が lean-toolchain を読み v4.30.0 を自動ダウンロードする
```

- `elan-init.sh` の取得（elan.lean-lang.org）は Claude Code のプロキシ環境で到達確認済み（2026-07-02）
- 2 行目の PATH 設定は**シェルを跨ぐたびに必要**（またはプロファイルに追記）
- `--default-toolchain none` にしているのは、既定 stable ではなくリポジトリ固定版だけを取らせるため

**失敗パターン**: `lake --version` の段階でツールチェーン本体のダウンロードが `403` や
`error: could not download file` で落ちる場合、**プロキシが GitHub リリース資材
（release.lean-lang.org → objects.githubusercontent.com へのリダイレクト先）を遮断している**。
→ §3 のネットワーク許可を設定するのが本筋。応急処置は方法 B/C。

## 2. 方法 B: リリース tarball の直接展開

```bash
# asset 名は環境により確認が必要（API が通るなら）:
curl -sL https://api.github.com/repos/leanprover/lean4/releases/tags/v4.30.0 \
  | grep browser_download_url | grep linux
# 出てきた linux x86_64 用 URL（例: lean-4.30.0-linux.tar.zst）を取得:
curl -LO <上で確認した URL>
mkdir -p $HOME/lean4 && tar --zstd -xf lean-4.30.0-linux*.tar.zst -C $HOME/lean4 --strip-components=1
# （.tar.gz 資材なら tar -xzf。zstd が無ければ apt-get install zstd 等）
export PATH="$HOME/lean4/bin:$PATH"
lean --version   # 4.30.0 を確認
```

方法 B も GitHub への到達が前提。**このドキュメント作成時のコンテナでは
github.com のリリース URL が一律 403 だった**（プロキシポリシー起因）ので、
その場合は §3 へ。

## 2.5 方法 C: Nix 経由（**GitHub 遮断環境で実証済みの経路**）

元コンテナの Lean はこの経路で入っている（`/nix/store/<hash>-lean4-4.30.0` に
nixpkgs ビルドの閉包が存在、apt/elan の痕跡なし）。**鍵となる事実（2026-07-03 検証）**:
Claude Code の既定プロキシは github.com のリリース資材を 403 で遮断する一方、
**パッケージ配布インフラは許可している** — cache.nixos.org / nixos.org /
install.determinate.systems / PyPI / archive.ubuntu.com はすべて 200 で到達可能。

```bash
# Nix をインストール（どちらも到達確認済み。single-user で十分）
curl -L https://nixos.org/nix/install | sh -s -- --no-daemon
. $HOME/.nix-profile/etc/profile.d/nix.sh
# lean4 を Nix バイナリキャッシュから取得（ビルドではなくキャッシュダウンロード）
nix profile install nixpkgs#lean4 --extra-experimental-features "nix-command flakes"
lean --version
```

**注意**: nixpkgs の lean4 の版は channel に依存する。`lean --version` が 4.30.0 で
なければ、4.30.0 を含む nixpkgs リビジョンを指定する:
```bash
# nixpkgs の履歴から lean4 = 4.30.0 のリビジョンを探して固定
nix profile install github:NixOS/nixpkgs/<rev>#lean4 ...
# github: 参照が遮断される場合は https://channels.nixos.org の tarball 指定で代替
```
版がどうしても合わない場合でも、まず入った lean で `lake build` を試す価値はある
（壊れたら `lean-toolchain` の版に合わせるのが原則 — §5 参照）。

## 3. 【本筋】環境のネットワークポリシー / セットアップスクリプト設定

「インストールできない」の典型原因はセッションのネットワークポリシーである。
Claude Code on the web の**環境（Environment）設定**で以下を行うのが恒久策:

1. **ネットワーク許可リスト**に以下のドメインを追加:
   - `elan.lean-lang.org`（インストーラ）
   - `release.lean-lang.org`（ツールチェーン配布のリダイレクタ）
   - `github.com` および `objects.githubusercontent.com` / `release-assets.githubusercontent.com`（リダイレクト先の実体）
2. **セットアップスクリプト**（環境起動時に毎回実行される）に方法 A を登録:
   ```bash
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:v4.30.0
   echo 'export PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile
   ```
   これで**全ての新セッションが最初から lean/lake を持って起動する**。
   ダウンロードは環境イメージ構築時の 1 回だけで済む。

環境設定の場所や書式は https://code.claude.com/docs/en/claude-code-on-the-web を参照。

## 4. インストール後の動作確認（必須）

```bash
cd <リポジトリ>/iut-lean-verification
lean --version          # Lean (version 4.30.0, ...) であること
lake build              # 初回はフルビルド（205 モジュール、数分〜十数分）。以降は差分のみ
bash build.sh           # 最後に "OK: all theorems verified, no sorry." が出ること
bash build.sh 2>/dev/null | grep -c Classical   # 意図的 Classical の台帳値（issue #48 §1.4 の基準値）と一致すること
```

3 つ揃えば環境構築完了。以降の開発手順は **issue #48（ロードマップ兼指示書）** に従う。

## 5. 注意事項

- **`lake update` は実行しない**（依存ゼロ。実行しても害は小さいが不要な manifest 変更が入り得る）
- `.lake/` はビルドキャッシュ（gitignore 済み）。消しても `lake build` で再生成される
- `lean-toolchain` を書き換えない。**v4.30.0 以外でのビルドは保証しない**（core API の名前が版で変わり、205 モジュールの証明が壊れ得る）
- インストールは最初の 1 回だけネットワークが要る。**ビルド・証明開発自体は完全オフラインで可能**
- `curl` が TLS エラーを出す場合はプロキシの CA バンドル設定（環境により `/root/.ccr/ca-bundle.crt` 等）を確認。`HTTPS_PROXY` を unset したり TLS 検証を切ったりしないこと

## 6. トラブルシュートまとめ

| 症状 | 原因 | 対処 |
|---|---|---|
| `curl ... elan-init.sh` が失敗 | プロキシが elan.lean-lang.org を遮断 | §3-1 の許可リスト追加 |
| elan は入ったが toolchain 取得で 403/timeout | GitHub リリース資材の遮断 | §3-1（github.com + *.githubusercontent.com） |
| `lean: command not found`（インストール直後） | PATH 未設定 | `export PATH="$HOME/.elan/bin:$PATH"`（新しいシェルごとに） |
| `lake build` が toolchain を再ダウンロードしようとする | 別バージョンが default になっている | リポジトリ直下で実行しているか確認（`lean-toolchain` が読まれる）。`elan toolchain list` で v4.30.0 の有無を確認 |
| ビルドが `unknown identifier` 等で大量エラー | Lean の版違い | `lean --version` を確認し v4.30.0 に固定 |
| GitHub は 403 だが何か入れたい | 既定プロキシはパッケージ配布インフラ（Nix キャッシュ・PyPI・apt）を許可している | §2.5 の Nix 経路（検証済み）を使う |
