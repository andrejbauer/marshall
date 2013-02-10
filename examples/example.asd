! This is a sample Marshall program.
! Comments begin with ! and end with end of line.
! Definitions and exprssions must be separated by double semicolons

let a = 2 * 3^4 + 0.01 - 1.12e-1
;;

! The identity function using cuts
let id = fun a : real => cut t left t < a right a < t
;;

! The square root function
let sqrt =
  fun a : real =>
    cut y 
      left  (y < 0 \/ y * y < a)

      right (y > 0 /\ y * y > a)
;;

! Square root of two
let a = sqrt 2
;;

! Compute the square of square root of 2
a^2
;;

! Square root of square root of 3
let b = sqrt (sqrt 3)
;;

! Cube roots of numbers in [0,1] exists up to precision 0.01
let p1 =
  forall x : [0,1], exists y : [0,1], x ={0.01}= y^3
;;

! There is an approximate solution of x^3 + 3 * x + 1 = 0
let p2 =
  exists x : real, x^3 + 3 * x + 1 ={0.00001}= 0
;;

! Testing comparisons
let p3 =
  forall x : [0,1], forall y : [0,1], x < y \/ y < x + 0.01
;;

! Logarithmic map
let lg = fun x : real => 2 * (1 - x^2) - 1
;;

! We have to iterate by hand because we do not have recursion yet
let lg2 = fun x : real => lg (lg x) ;;
let lg4 = fun x : real => lg2 (lg2 x) ;;
let lg8 = fun x : real => lg4 (lg4 x) ;;
let lg16 = fun x : real => lg8 (lg8 x) ;;
let lg32 = fun x : real => lg16 (lg16 x) ;;
let lg64 = fun x : real => lg32 (lg32 x) ;;

! Now compute lg64 0.1.
let c = lg16 0.1 ;;


! Maximum of a function on the unit interval
let max =
  fun f : real -> real =>
    cut a
      left  (exists x : [0,1], a < f x)
      right (forall x : [0,1], f x < a)
;;

!! The next one is rather slow

let u = max (fun x : real => x * (1 - x))
;;

let v = max sqrt ;;

let w = max (fun x:real => 0.00756*x - 0.0726*x^2 + 0.299667*x^3 - 0.5675*x^4 + 0.5*x^5 - 0.166667*x^6);;
