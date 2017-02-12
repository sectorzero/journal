#!/bin/sh

# Data transformation steps
# 
# Input CSV File 
# Day,Food Name,Amount,Energy (kcal),Alcohol (g),Caffeine (mg),Water (g),B1 (Thiamine) (mg),B12 (Cobalamin) (µg),B2 (Riboflavin) (mg),B3 (Niacin) (mg),B5 (Pantothenic Acid) (mg),B6 (Pyridoxine) (mg),Folate (µg),Vitamin A (IU),Vitamin C (mg),Vitamin D (IU),Vitamin E (mg),Vitamin K (µg),Calcium (mg),Copper (mg),Iron (mg),Magnesium (mg),Manganese (mg),Phosphorus (mg),Potassium (mg),Selenium (µg),Sodium (mg),Zinc (mg),Carbs (g),Fiber (g),Starch (g),Sugars (g),Fat (g),Cholesterol (mg),Monounsaturated (g),Omega-3 (g),Omega-6 (g),Polyunsaturated (g),Saturated (g),Trans-Fats (g),Cystine (g),Histidine (g),Isoleucine (g),Leucine (g),Lysine (g),Methionine (g),Phenylalanine (g),Protein (g),Threonine (g),Tryptophan (g),Tyrosine (g),Valine (g)
# 2016-9-26,"Bear Naked Granola Fruit and Nut","0.52 Serving (22 tsp, whole pieces)",133.64,0.00,0.00,3.19,0.09,0.00,0.07,0.31,0.21,0.03,7.37,0.85,0.09,0.00,1.02,1.96,8.34,0.13,0.68,32.02,0.75,83.94,100.01,4.92,2.00,0.76,17.00,2.34,8.73,5.69,6.63,0.00,2.87,0.33,1.61,1.95,1.43,0.01,0.08,0.06,0.11,0.21,0.12,0.04,0.14,2.85,0.09,0.04,0.08,0.14
# 
# Transformation : 
# cat servings-20160925-20161125.csv | sed 's/".*"/null/g' | awk -F',' '{ consumed[$1] += $3; } END{ for (k in consumed) print k, " ", consumed[k]; }' | egrep -v "^Day" > consumed-20160925-20161125.log
# sed -i '.tmp' 's/-\([0-9]\)\([ -]\)/-0\1\2/' consumed-20160925-20161125.log
# 
# Output:
# 2016-09-26   1229.01
# 2016-09-27   786.26
# 
# Combining :
# Final Legend : Date,Weight_Kgs,Net_KCal,Consumed_KCal,Burned_KCal,BasalMetabolism_KCal,GeneralActivity_KCal
# join -a 1 -a 2 -e'0.0' -o '0,1.2,2.2' consumed-20160925-20161125.log burned-20160925-20161125.log | awk '{print $1 " " $2 " " $3 " -880.0 -170.0"}' > combined-20160925-20161125.tmp
# join -a 1 -a 2 -e'---' -o '0,2.2,1.2,1.3,1.4,1.5' combined-20160925-20161125.tmp weight-20160925-20161125.log
# cat combined-20160925-20161125.log| awk '{total_out=$4+$5+$6; total_in=$3; net=total_in+total_out; print $1 "," $2 "," net "," total_in "," total_out "," $4 "," $5 "," $6}' > combined-20160925-20161125.log.tmp
# <manual fill / corrections>
# 
# Final Output
# Date,Weight_Kgs,Net_KCal,TotalInput_KCal,TotalOutput_KCal,Exercise_KCal,BasalMetabolism_KCal,GeneralActivity_KCal
# 2016-09-25,77.0,450,1500.00,-1050,0.0,-880.0,-170.0
# 2016-09-26,76.9,111.63,1229.01,-1117.38,-67.38,-880.0,-170.0
# 2016-09-27,76.4,-489.5,786.26,-1275.76,-225.76,-880.0,-170.0

servings=$1
exercises=$2
biometrics=$3
destpath=$4

cat $servings \
    | sed 's/".*"/null/g' \
    | awk -F',' \
        '{ consumed[$1] += $3; } END{ for (k in consumed) print k, " ", consumed[k]; }' \
    | egrep -v "^Day" \
    | sed 's/-\([0-9]\)\([ -]\)/-0\1\2/' \
    | sed 's/-\([0-9]\)\([ -]\)/-0\1\2/' \
    | sort -k 1 \
    > consumed.log

cat $exercises \
    | sed 's/".*"/null/g' \
    | awk -F',' \
        '{ burned[$1] += $4; } END{ for (k in burned) print k, " ", burned[k]; }' \
    | egrep -v "^Day" \
    | sed 's/-\([0-9]\)\([ -]\)/-0\1\2/' \
    | sed 's/-\([0-9]\)\([ -]\)/-0\1\2/' \
    | sort -k 1 \
    > burned.log

cat $biometrics \
    | egrep -v "^Day" \
    | egrep 'Weight' \
    | awk -F',' '{print $1 " " $4}' \
    | sed 's/-\([0-9]\)\([ -]\)/-0\1\2/' \
    | sed 's/-\([0-9]\)\([ -]\)/-0\1\2/' \
    | sort -k 1 \
    > weight.log

lines_consumed=$(wc -l consumed.log)
lines_burned=$(wc -l burned.log)
lines_weight=$(wc -l weight.log)

#if [ ( $lines_consumed -ne $lines_burned ) && 
#     ( $lines_consumed -ne $lines_weight ) ]; then
#     exit 1
#fi

bmr=-880.0
dar=-170.0
join -a 1 -a 2 -e'0.0' -o '0,1.2,2.2' \
    consumed.log burned.log \
    | awk '{print $1 " " $2 " " $3 " -880.0 -170.0"}' \
    > combined_1.tmp
join -a 1 -a 2 -e'---' -o '0,2.2,1.2,1.3,1.4,1.5' \
    combined_1.tmp weight.log \
    > combined_2.tmp
cat combined_2.tmp \
    | awk '{total_out=$4+$5+$6; total_in=$3; net=total_in+total_out; print $1 "," $2 "," net "," total_in "," total_out "," $4 "," $5 "," $6}' \
    > combined_3.tmp

# legend='Date,Weight_Kgs,Net_KCal,TotalInput_KCal,TotalOutput_KCal,Exercise_KCal,BasalMetabolism_KCal,GeneralActivity_KCal'
# echo $legend > combined.log
cat combined_3.tmp > combined.log

echo "Date,Weight-Kgs" > $destpath/q72_weight.csv
awk -F',' '{print $1 "," $2 "," 0.5}' combined.log >> $destpath/q72_weight.csv

echo "Date,Net-kCal" > $destpath/q72_netcal.csv
awk -F',' '{print $1 "," $3 "," 100}' combined.log >> $destpath/q72_netcal.csv

echo "Date,Input,Output" > $destpath/q72_detailcal.csv
awk -F',' '{print $1 "," $4 "," 100 "," $5 "," 100}' combined.log >> $destpath/q72_detailcal.csv

# cd $destpath & git status
