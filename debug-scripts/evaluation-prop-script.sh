# A script that takes a formula output together with a satisfying encoding, and uses limboole to check one by line if it is really a satisfying encoding
# This script ONLY really checks the lines which can be parsed by limboole by a simple preprocessing. All the other lines are output in
# a dedicated file tmp/formula.limboole, so that the user can inspect what was missed.

# Usage: set limboole variable in this script to point to limboole
#   create "tmp" subdirectory of the current directory
#   run this script with 2 parameters, first being formula obtained by running isp with -C param, the second being the file to which isp output was redirected (in particular is must contain an assingment) 

limboole=limboole
#rewrite the file with assignment to a limbool-format file, and store it
cat $2 | grep ":[10]" | sed "s/\(.*\):0/!\1 \&/" | sed "s/\(.*\):1/\1 \&/" > tmp/valuations.txt
#cleanup (remove "()" and binary operators followed by parentheses) in the formula and 
#go through all lines of the formula file
A=0
rm tmp/formula.limboole
cat $1 | sed "s/()//g" | sed "s/[&|][ ]*)/)/g" | sed "s/[&|][ ]*$//g" | while IFS= read -r line; do
 #for each line in the formula file
 A=$((A+1));
 #create a file for the line in whihch we store the valuation
 cp tmp/valuations.txt tmp/$A.limboole
 #...and constants
 echo "1 &" >> tmp/$A.limboole
 echo "!0 &" >> tmp/$A.limboole
 #...and the line of the formula file itself
 echo $line >> tmp/$A.limboole

 #check if the file created gives rise to a satisfiable formula, if not, shout.
 #note: lot of formula-file lines are debug garbage or hard to parse. In this case limboole will complain with a return error code, so we use &&
 ($limboole -s tmp/$A.limboole 2>/dev/null | grep -q UNSATISFI) && echo "Line $A contains a problematic subformula"

 #for debug purposes we output the unparsed lines to a separate file
 $limboole -s tmp/$A.limboole 2>/dev/null || (echo $line >> tmp/formula.limboole)
done

