  for f in self_tests/*.scm; do 
  ocaml compiler.ml $f > out.s
  nasm -f elf64 -o out.o out.s
  gcc -no-pie -m64 -o out out.o
  our=`./out`
  retVal=$?
  petite=`cat $f | petite -q`
  result=""
  if [ $retVal -eq 1 -o $retVal -eq 94 ]; then
      if [ "$our" = "$petite" ]; then
        result="#t"
      else
        result=`echo "(equal? '$our '$petite)" | petite -q`
      fi

      if [ "$result" = "#t" ]; then
          echo "Test $f Passed"
          rm out out.o
      else
          echo "*** RESULTS DIFFER in $f"
          echo "*** scheme output: $petite"
          echo "*** our output: $our"
          rm out out.o
      fi
  else
   echo "*** ERROR in $f"
   echo "got error code: $retVal" 
  rm out out.o
  fi
done