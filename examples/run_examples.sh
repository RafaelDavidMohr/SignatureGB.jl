module load julia;
for f in *.jl
do
    if !(test -f "$f.log"); then
	echo "starting $f";
	julia $f > $f.log
    fi
done
