# algoveri
codebase for verification benchmark of intro to algo

# Instruction for Testing the Codebase

## Setting up verifiers

Create a common folder that stores all the images, all the used compilers, etc

```bash
mkdir -p apptainer_imgs
```

### Dafny

Just pull the pre-build image from the web. This image use Dafny 4.11

```bash
cd apptainer_imgs
apptainer pull dafny.sif docker://xtrm0/dafny
```

### Rust+verus

Similar to Dafny, we first pull the pre-build image from the web.

```bash
# cd apptainer_imgs if not in apptainer_imgs folder
apptainer pull verus.sif docker://ghcr.io/principled-systems/verus
```

Next, create folders to store the necessary toolchain files

```bash
mkdir -p rust_home/cargo
mkdir -p rust_home/toolchains
```

Run the installer to solve the version issue

```bash
apptainer exec \
  --bind $PWD/rust_home/cargo:/rust/cargo \
  --bind $PWD/rust_home/toolchains:/rust/toolchains \
  --env CARGO_HOME=/rust/cargo \
  --env RUSTUP_HOME=/rust/toolchains \
  verus.sif \
  bash -c "curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain 1.79.0"
```

The whole script can be found at `script/verus.sh`

### Lean

