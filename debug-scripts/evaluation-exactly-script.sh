#A script that checks if some m <-> exactly(k, S) formula is violated
#and (see the last if below) if for some formula of the above form it
#is the case that the number of satisfied propositions in S is > k.

#Usage:
# * Run mopper (isp) with -C option, that will create a *formula file.
#   Also redirect the output to a separate file, so that we can access
#   it to get a satisfying valuation
# * Then run 
#   ./script formula_file mopper_output_redirected_file



# go through all lines which contain the "m<-> exactly" subformula
grep "{" $1| while IFS= read -r line; do
 #for each line...

 #extract the name of M atomic proposition for the call (e.g. M_01)
 CALL=`echo $line | sed "s/.*\(M_[0-9]*\).*/\1/"`;

 #extract the cardinality for the call 
 CARDINALITY=`echo $line | sed "s/.*<->(\([0-9]*\),.*/\1/"`

 #extract the "S_..." variables for potential matches, as comma-separated list 
 COMMAMATCHES=`echo $line | sed "s/.*{\(.*\),}.*/\1/"`

 #turn the list into space-separated
 SPACEMATCHES=`echo $COMMAMATCHES | tr ',' ' '`

 #go through the list and count number of "S_..." propositions that are true, i.e. number of matches
 COUNT=0
 for S in $SPACEMATCHES; do
  grep "$S:1" $2 > /dev/null && COUNT=$((COUNT+1));
 done

 #determine if the M_XY proposition is true
 VAL=`grep "$CALL:" $2 |sed "s/.*$CALL:\(.\).*/\1/"`

 if [ $VAL -eq 0 ]; then  
   if [ $COUNT -eq $CARDINALITY ]; then
    #if the proposition is false and cardinality is equal, print it as error
    echo "$CALL is false, but while it has cardinality $CARDINALITY, number of matches is $COUNT"
   fi
 else
   if [ $COUNT -ne $CARDINALITY ]; then
    #if the proposition is true and cardinality is not equal, print it as error
    echo "$CALL is true, but while it has cardinality $CARDINALITY, number of matches is $COUNT"
   fi
 fi

 #check if the number of satisfied propositions is too large. This would not violate the exactly formula,
 #but the corresponding atmost formula (we use this as a hack since atmost and exactly formulas in multirecv
 #encoding have the same parameters).
 if [ $VAL -gt $CARDINALITY ]; then
    echo "The restriction corresponding to match $CALL has $CARDINALITY, number of matches is $COUNT"
 fi
done
