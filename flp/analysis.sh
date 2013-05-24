#!/bin/bash
set -o nounset -o errexit -o pipefail

function patch_cabal() {
    local cabal_file="$(echo *.cabal)"

    sed -i -s '/^library/I {
        n
        h
        s/[^ ].*/build-depends: what-morphism/p
        s/[^ ].*/ghc-options: -fplugin WhatMorphism/p
        g
    }' "$cabal_file"
}

function report() {
    local log="$1"
    local tmp="$(mktemp)"
    (fgrep WhatMorphismResult "$log" || true) >"$tmp"
    echo "Total: $(wc -l <"$tmp")"
    echo "List: $((fgrep '[]' "$tmp" || true) | wc -l)"
    echo "ADT: $((fgrep -v '[]' "$tmp" || true) | wc -l)"
    echo "Changing: $((fgrep 'ChangingArgs' "$tmp" || true) | wc -l)"
    echo "Nested: $((fgrep 'NestedRec' "$tmp" || true) | wc -l)"
    rm "$tmp"
}

function compile() {
    local root="$(pwd)"
    local dir="$1"
    local log="what-morphism.log"
    cd "$dir"

    echo "Patching cabal file..."
    patch_cabal

    echo "Compiling..."
    if cabal configure && cabal build >"$log" 2>&1; then
        echo "Compilation OK"
        report "$log"
    else
        echo "Compilation failed"
        cd "$root"
        exit 1
    fi
}

if [[ $# < 1 ]]; then
    echo "Usage: $0 <package>"
    exit 1
else
    tar -xzf "$1"
    compile "$(echo "$1" | sed 's/.tar.gz$//')"
fi
