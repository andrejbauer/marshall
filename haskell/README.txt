To create HTML documentation in the doc subdirectory run

   haddock -o doc -h *.hs

To run the package for real number computation, load Reals.hs in Haskell shell.
Here is an example session.

GHCi, version 6.10.4: http://www.haskell.org/ghc/  :? for help
Loading package ghc-prim ... linking ... done.
Loading package integer ... linking ... done.
Loading package base ... linking ... done.
Prelude> :load Reals.hs
[1 of 5] Compiling Staged           ( Staged.hs, interpreted )
[2 of 5] Compiling Space            ( Space.hs, interpreted )
[3 of 5] Compiling Dyadic           ( Dyadic.hs, interpreted )
[4 of 5] Compiling Interval         ( Interval.hs, interpreted )
[5 of 5] Compiling Reals            ( Reals.hs, interpreted )
Ok, modules loaded: Interval, Reals, Dyadic, Staged, Space.
*Reals> let a = exact 1.3
Loading package syb ... linking ... done.
Loading package array-0.2.0.0 ... linking ... done.
Loading package filepath-1.1.0.2 ... linking ... done.
Loading package old-locale-1.0.0.1 ... linking ... done.
Loading package old-time-1.0.0.2 ... linking ... done.
Loading package unix-2.3.2.0 ... linking ... done.
Loading package directory-1.0.0.3 ... linking ... done.
Loading package process-1.0.1.1 ... linking ... done.
Loading package random-1.0.0.1 ... linking ... done.
Loading package haskell98 ... linking ... done.
*Reals> a * (1 - a)
[-1635786*2^-22,-1635768*2^-22] -0.3899996280670166
*Reals> a ^ 200
[1705561*2^55,1706556*2^55] 6.146723539897814e22
*Reals> forall (ClosedInterval (0,1)) $ \x -> (x * (1 - x)) `less` exact 0.26
True
*Reals> forall (ClosedInterval (0,1)) $ \x -> (x * (1 - x)) `less` exact 0.24
False
