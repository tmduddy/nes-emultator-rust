# nes-emulator-rust

## Introduction
This is a project that I've been interersted in for years, since finding the wonderful C++ implementation documented on YouTube by javidx9 [here](https://www.youtube.com/watch?v=F8kx56OZQhg).

If you haven't seen that series before, you should watch it. Even as someone with only the bare minimum knowledge of C/C++ it was a really informative and fun series to follow along with and definitely gave me the foundation needed to confidently take on this project.

In the last few weeks I've been trying to learn Rust and stumbled upon bugzmanov's NES emulator in Rust tutorial [here](https://bugzmanov.github.io/nes_ebook/chapter_1.html).

This repo is my following along of that tutorial. I like that it isn't a fully line-by-line guide but rather allows the reader to experiment and implement features following their own preferred design patterns. I'm imaging this as something I'll want to revisit as my language knowledge increases so that I can refactor and refine it further.

## Running
Note: currently I've only tested this on an M3 Macbook Pro running MacOS Tahoe (26.2). I'd like to try compiling for more systems in the future.

```
cargo build [--release]
./target/dev/nes-emulator-rust
# or
./target/release/nes-emulator-rust
```

## Testing
Unit tests are available and can be run with 
```
cargo test
```

## Documentation
I'm trying to keep up with documenting key attributes and methods, if only for my own education.
```
cargo doc --open
```

## Sources
- bugzmanov's NES emulator in Rust tutorial: [link](https://bugzmanov.github.io/nes_ebook/chapter_1.html)
- javidx9's NES emulator in C++ series: [link](https://www.youtube.com/watch?v=F8kx56OZQhg)
