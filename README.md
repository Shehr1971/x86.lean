# x86.lean

This is a tiny educational x86 compiler, written in lean, more or less 
following the design of the [Essentials of Compilation Book](
https://github.com/IUCompilerCourse/Essentials-of-Compilation).

The input language is a mini-racket, with new features added 
chapter-by-chapter.

## Usage

To simply compile to assembly:

```
my_file.src | lake exec compiler > my_file.s
```

To build an executable binary, linking against stdlib for `scanf` and `printf`, 
put your source code in `out.src` and

```
make
```
