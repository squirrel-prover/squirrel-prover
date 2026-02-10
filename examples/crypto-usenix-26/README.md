This directory contains the Squirrel developments for the Usenix'26 paper 

```
Leveraging Cryptographic Simulator Synthesis for
Formally Verifying the FOO E-Voting Protocol
```

The Squirrel developments include:
- the motivating example, in `motivating.sp`
- the KDF example in `kdf.sp`
- the memoization examples in `memoization.sp`
- the NSL example in `nsl.sp`
- the proof of ballot privacy for FOO in `foo/`
  + the main security lemma is in `foo/main.sp`
  + see `foo/README.md` for a quick guided tour of the proof
  
