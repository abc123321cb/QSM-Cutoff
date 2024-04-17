for FILE in *.ivy;
do
    echo "$FILE";
    c="${FILE%.*}"
    c+=".log"
    python3 ../qrm.py -i $FILE > $c
done