module Dyadic_test =
  functor (D:Dyadic.DYADIC) ->
    struct
      let test_oftostr s =
	D.to_string (D.of_string s)

      let print_strtest s =
	((test_oftostr s) ^ "==" ^ s)

      let test_str s = 
	print_endline s ;
	print_endline (print_strtest "2e-10") ;
	print_endline (print_strtest "2e-8") ;
	print_endline (print_strtest "2e-7") ;
	print_endline (print_strtest "2e-6") ;
	print_endline (print_strtest "2e-5") ;
	print_endline (print_strtest "2e-1") ;		
	print_endline (print_strtest "2") ;	
	print_endline (print_strtest "2e10") ;	
	print_endline (print_strtest "2e16") ;	
	print_endline (print_strtest "2e17") ;
	print_endline (print_strtest "2e18") ;
	print_endline (print_strtest "0.123456") ;
	print_endline (print_strtest "2e3") ;
	print_endline (print_strtest "-2e18") ;
	print_endline (print_strtest "-0.123456") ;
	print_endline (print_strtest "-2e-3") ;	

	print_endline (D.to_string (D.add ~round:D.down (D.make_int ~round:D.down 1 (-1)) (D.make_int ~round:D.down 20 0))) ;
	print_endline (D.to_string (D.add ~round:D.down D.one (D.of_string "2e3"))) ;
	print_endline (D.to_string (D.sub ~prec:10 ~round:D.down D.one (D.of_string "0.123456"))) ;
	print_endline (D.to_string (D.mul ~prec:10 ~round:D.down D.one (D.of_string "0.123456"))) ;
	print_endline (D.to_string (D.div ~prec:10 ~round:D.down D.one (D.of_string "3"))) ;
	print_endline (D.to_string (D.div ~prec:10 ~round:D.down D.one (D.of_string "2")))
    end;;


module T1=Dyadic_test(Dyadic_mpfr)
module T2=Dyadic_test(Dyadic_bignum)

let main =  
  T1.test_str "Test mpfr";  
  T2.test_str "Test bignum"