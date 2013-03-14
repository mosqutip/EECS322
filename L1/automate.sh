rm -f a.out
rm -f prog.S
rm -f prog.temp
rm -f x.L1
rm -f runtime.o

for file in *.L1
do
	echo "Compiling $file"
	rm -f a.out
	./L1c $file
	echo "Running compiled $file"
	./a.out
done

rm -f a.out
rm -f prog.S
rm -f prog.temp
rm -f x.L1
rm -f runtime.o
