#!/bin/bash

if [ `uname -m` == "i686" ]; then
	GP2C_OPTS="-3"
else
	GP2C_OPTS=""
fi
GP2C="`pwd`/../gp2c -R $GP2C_OPTS"
ISO="`pwd`/../IsoChecker"


failure () {
	echo -e "\e[31m failure\e[0m"
}

success () {
	echo -e "\e[32m success\e[0m"
}

solution_exists () {
	if [ ! -f Solutions/$1.out ]; then
		echo -e "\e[33m no solution found\e[0m"
		false
	fi
}
ok () {
	echo -n "."
}
isocheck () {
	for f in Solutions/$1.out* ; do 
		$ISO $2 $f
	done | grep "^ISOMORPHIC"
}


run_test () {
	d=$1
	p=${d%%/}
	pushd $d > /dev/null
	for t in *.host ; do
		echo -n "Testing $t in $d	"
		if solution_exists $t; then
			( $GP2C $p.gp2 $t && ./$p > /tmp/$p.out && isocheck $t /tmp/$p.out ) > /dev/null 2>&1 && success || failure
		fi
	done
	rm -f $p $p.c
	popd > /dev/null
	
}


if [ -z "$1" ]; then 
	for d in */ ; do
		run_test $d
	done
else
	run_test $1
fi

