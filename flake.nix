{
  description = "CA - Content-Addressing for Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Lean 4 release binary. Keep `leanVersion` equal to
        # `lean-toolchain` (leanprover/lean4:v4.35.0) and refresh the
        # four hashes together:
        #   curl -sL https://github.com/leanprover/lean4/releases/download/v$V/lean-$V-$P.tar.zst \
        #     | sha256sum | cut -d' ' -f1 | xxd -r -p | base64      # → sha256-…
        # (or `nix hash file` on the downloaded tarball).
        leanVersion = "4.35.0";
        leanPlatform = {
          "x86_64-linux"   = "linux";
          "aarch64-linux"  = "linux_aarch64";
          "x86_64-darwin"  = "darwin";
          "aarch64-darwin" = "darwin_aarch64";
        }.${system} or (throw "CA: no Lean release tarball for ${system}");
        leanSha256 = {
          "linux"          = "sha256-colZekRUMkbJInuMrlAXZ+CVzhf21Ei5X8So3Jcmj20=";
          "linux_aarch64"  = "sha256-yPD4o5IOg5cYsTQ+Z4H9gKPpsQJPvNcHjrMPVOgGsCg=";
          "darwin"         = "sha256-C0O+XH7Ps2AWVmpBAFq2K9sEdD5r/Vg35F95bvR1C04=";
          "darwin_aarch64" = "sha256-wMbzTzW6HcxcSl/RBv76uetehGlxJiTdLIaNUbYxd8I=";
        }.${leanPlatform};

        lean4Bin = pkgs.stdenv.mkDerivation {
          pname = "lean4";
          version = leanVersion;
          src = pkgs.fetchurl {
            url = "https://github.com/leanprover/lean4/releases/download/v${leanVersion}/lean-${leanVersion}-${leanPlatform}.tar.zst";
            sha256 = leanSha256;
          };
          nativeBuildInputs = [ pkgs.zstd ]
            ++ pkgs.lib.optionals pkgs.stdenv.isLinux [ pkgs.autoPatchelfHook ];
          buildInputs = pkgs.lib.optionals pkgs.stdenv.isLinux [ pkgs.stdenv.cc.cc.lib pkgs.zlib ];
          unpackPhase = ''
            tar --zstd -xf $src
          '';
          installPhase = ''
            mkdir -p $out
            cp -r lean-${leanVersion}-${leanPlatform}/* $out/
          '';
        };

        # Library path variable name (different on Darwin vs Linux)
        libPathVar = if pkgs.stdenv.isDarwin then "DYLD_LIBRARY_PATH" else "LD_LIBRARY_PATH";

        # Native dependencies.
        #   CA library : none (pure Lean)
        #   ca CLI     : OpenSSL (cli/c/sha256_shim.c), hiredis + zlog via
        #                redis-lean / zlog-lean, zstd for arrow-lean's pure-C
        #                Parquet code (pulled in by redis-lean; no arrow-cpp)
        #                — see docs/building.md
        libDeps = [
          pkgs.openssl
          pkgs.hiredis
          pkgs.zlog
          pkgs.zstd
        ];
        nativeDeps = libDeps ++ [ pkgs.gmp pkgs.libuv ];   # Lean runtime

        # The CLI's link lines name the Ubuntu paths
        # (`-L/usr/lib/x86_64-linux-gnu`, `-L/usr/local/lib`). On NixOS and
        # macOS they do not exist and the shell's libraries are used. On a
        # non-NixOS Linux they come first, so the binary may link the host's
        # libraries instead: it runs on that host, but the build is not
        # hermetic there.
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = nativeDeps ++ [
            lean4Bin
            pkgs.clang
            pkgs.lld
            pkgs.git       # lake fetches the git requires
            pkgs.redis     # `redis-server` for the ca CLI's fetch/address (optional)
          ];

          LIBRARY_PATH = pkgs.lib.makeLibraryPath nativeDeps;
          C_INCLUDE_PATH = pkgs.lib.makeSearchPath "include" [
            pkgs.openssl.dev
            pkgs.hiredis
            pkgs.zlog
            pkgs.zstd.dev
          ];

          shellHook = ''
            export ${libPathVar}="${pkgs.lib.makeLibraryPath nativeDeps}"
            echo "CA development environment — Lean $(lean --version 2>/dev/null | sed 's/^Lean (version //; s/,.*//' || echo 'not found'), toolchain pin $(cat lean-toolchain 2>/dev/null)"
          '';
        };
      }
    );
}
