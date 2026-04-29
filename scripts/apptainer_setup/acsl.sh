# Build the ACSL / Frama-C apptainer image from the recipe.
#
# Run this from your apptainer_imgs/ directory (per VERIFIER_README.md).
# The recipe ships next to this script under scripts/apptainer_setup/acsl.def.
#
# Build takes ~15-30 min (opam compiles OCaml 5.2.0 from source). Image ~2 GB.

DEF="$(cd "$(dirname "$0")" && pwd)/acsl.def"

apptainer build acsl.sif "$DEF"
# If you don't have root and your cluster admin hasn't enabled fakeroot:
# apptainer build --fakeroot acsl.sif "$DEF"
