#!/bin/bash
# Generate memory-limited wrappers for the external provers Sledgehammer runs.
#
# SUPERSEDED by the Isabelle component in this repository - see README.md,
# "Sledgehammer exhausting machine memory". That does the same job without
# generating anything: etc/settings points the prover variables at the wrappers
# in contrib/prover_wrappers, so the memory policy is version-controlled and
# travels with the repository instead of living in $HOME. Prefer it.
#
# This script is kept for machines where registering a component is not wanted,
# and because it is what the measurements below were taken with. It writes into
# $HOME and prints settings lines for you to paste, so nothing it does is
# reproducible from a checkout alone.
#
# Why this exists
# ---------------
# Sledgehammer launches every prover in the "sledgehammer_provers" option
# concurrently, as external processes.  Isabelle bounds their *time* but not
# their *memory*: veriT, for instance, is invoked with only --max-time (see
# veriT_options in ~~/src/HOL/Tools/SMT/smt_systems.ML).  A prover that starts
# diverging therefore allocates freely until either it finishes, its time budget
# expires, or the machine runs out of memory.
#
# That last outcome dominated the recorded TIP15 evaluation: 148 of the 176
# abduction/preprocessed_abduction failures were memory exhaustion rather than a
# prover verdict.  Measured on TIP_sort_NStoogeSort2Count, a *single* veriT
# process reached 6.35GB while the Isabelle ML process held only 1.9GB -- so
# capping the ML heap alone does not help, it merely leaves more room for the
# provers to take.
#
# Each wrapper puts the real binary in a cgroup with a resident-memory ceiling
# and then execs it, so a diverging prover is killed instead of the whole
# evaluation.  Sledgehammer records that prover as having failed and carries on
# with the others.
#
# !! EXPERIMENTAL - AN EARLIER MECHANISM COST PROOFS; THIS ONE IS NOT YET
#    MEASURED.  DO NOT ENABLE BY DEFAULT !!
# ----------------------------------------------------------------------
# The first version of this script used "ulimit -v".  It did bound memory: on
# four previously-SIGKILLed TIP15 targets the peak dropped by 1.4-3.6GB.  But it
# also lost proofs.  On TIP_sort_SSortCount, same machine, everything else equal:
#
#   no wrappers        proof found (485s), and again on a repeat (600s)   2/2
#   wrappers @1500MB   no proof (615s)                                    0/2
#   wrappers @3500MB   no proof (711s)
#
# Raising the limit did not bring the proof back, so it was not simply too small
# a budget.  Two weaknesses were identified:
#
#   - "ulimit -v" caps *virtual* address space, not resident memory.  A solver
#     that reserves a large address range up front while touching little of it
#     is killed for allocations it never really made.  Measured RSS on a trivial
#     query is only 3-15MB for z3/cvc5/veriT, so the cap could not be calibrated
#     from observed RSS at all.
#   - Some Isabelle prover entries are launcher scripts that depend on companion
#     settings (cvc5 runs "$CVC5_HOME/cvc5-bin"), so redirecting one setting
#     without the other is fragile.
#
# This version addresses the first and not the second.  A cgroup MemoryMax bounds
# *resident* memory, so a solver is charged for what it touches rather than for
# what it reserves - which is exactly the difference that made the ulimit numbers
# uninterpretable.  Whether that recovers TIP_sort_SSortCount is unmeasured, and
# that target is the acceptance test: it must go back to 2/2 before this is worth
# anything.  Until then the validated way to keep these evaluations alive remains
# the ML heap ceiling plus the hammer budget (see Eval/run_eval.sh), which
# converted every SIGKILL tested into a completed run, recovered four targets as
# real proofs, and left 6/6 previously-succeeding targets still succeeding.
#
# The limit here should agree with the "hammer_memory_quota_mb" config in
# PSL/Resource_Limit.ML, which divides the machine's memory by the same number to
# decide how many hammers may run at once.  One quota, two jobs: admission
# control there, enforcement here.  If they disagree, the search admits more
# concurrent provers than the machine has ceilings for.
#
# Provers whose Isabelle setting names a *directory* rather than an executable
# are handled by building a shadow directory: every entry of the original is
# symlinked across (auxiliary binaries and bundled shared libraries such as
# zipperposition's libgmp.so.10 must stay resolvable) and only the main
# executable is replaced by the wrapper.
#
# Usage:
#   Eval/make_prover_memory_wrappers.sh [LIMIT_MB] [WRAPPER_DIR]
# then append the printed lines to $ISABELLE_HOME_USER/etc/settings.
set -euo pipefail

LIMIT_MB="${1:-2048}"
WRAPPER_ROOT="${2:-$HOME/.isabelle/prover_wrappers}"
ISABELLE="${ISABELLE:-isabelle}"

# Kept for the fallback path only; the cgroup ceiling is expressed in megabytes.
LIMIT_KB=$((LIMIT_MB * 1024))

# "<setting>:<kind>:<executable>" where kind is exe (setting names the binary)
# or dir (setting names the directory containing it).
SPECS="
ISABELLE_VERIT:exe:
Z3_SOLVER:exe:
CVC5_SOLVER:exe:
E_HOME:dir:eprover
VAMPIRE_HOME:dir:vampire
SPASS_HOME:dir:SPASS
ZIPPERPOSITION_HOME:dir:zipperposition
"

mk_wrapper () {  # $1 = real binary, $2 = wrapper path
  cat > "$2" <<EOF
#!/bin/bash
# PSL prover memory wrapper -- generated by Eval/make_prover_memory_wrappers.sh
#
# A transient cgroup scope with a resident-memory ceiling. MemorySwapMax=0 as
# well, because a ceiling a solver can page around is not a ceiling. --collect so
# the scope is reaped when the prover exits, rather than accumulating one failed
# unit per invocation over a run of thousands.
#
# The guard is on the user bus, not on systemd-run alone: a detached run may have
# no session bus, and a prover that cannot start is worse than one that is not
# capped. Falling back to "ulimit -v" keeps some bound in that case, with the
# caveat recorded in the generator that it is an address-space bound and is what
# the earlier measurements found uninterpretable.
if command -v systemd-run >/dev/null 2>&1 \\
   && [ -n "\${XDG_RUNTIME_DIR:-}" ] && [ -S "\${XDG_RUNTIME_DIR}/bus" ]; then
  exec systemd-run --user --scope -q --collect \\
       -p MemoryMax=${LIMIT_MB}M -p MemorySwapMax=0 -- "$1" "\$@"
fi
ulimit -v $LIMIT_KB 2>/dev/null || true
exec "$1" "\$@"
EOF
  chmod +x "$2"
}

mkdir -p "$WRAPPER_ROOT"
{
  echo "# Append to $($ISABELLE getenv -b ISABELLE_HOME_USER)/etc/settings"
  echo "# Wrappers under $WRAPPER_ROOT, limit ${LIMIT_MB}MB of virtual memory each."
  echo
} >&2

for spec in $SPECS; do
  var="${spec%%:*}"; rest="${spec#*:}"; kind="${rest%%:*}"; exe="${rest#*:}"
  target="$($ISABELLE getenv -b "$var" 2>/dev/null || true)"
  [ -n "$target" ] || continue
  # Idempotence: never wrap something already living under the wrapper root.
  case "$target" in "$WRAPPER_ROOT"*) continue ;; esac

  if [ "$kind" = exe ]; then
    [ -x "$target" ] || continue
    wrapper="$WRAPPER_ROOT/$(basename "$target")"
    mk_wrapper "$target" "$wrapper"
    echo "$var=\"$wrapper\""
  else
    [ -x "$target/$exe" ] || continue
    # Keyed by setting name, not by basename: every bundled prover directory is
    # called after the platform (x86_64-linux), so basenames would all collide
    # into one shadow and the last prover processed would clobber the rest.
    shadow="$WRAPPER_ROOT/$var"
    rm -rf "$shadow"; mkdir -p "$shadow"
    # Symlink everything, then override the one executable we are limiting.
    for entry in "$target"/*; do
      [ -e "$entry" ] && ln -sfn "$entry" "$shadow/$(basename "$entry")"
    done
    rm -f "$shadow/$exe"
    mk_wrapper "$target/$exe" "$shadow/$exe"
    echo "$var=\"$shadow\""
  fi
done
