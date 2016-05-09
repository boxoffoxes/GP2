#!/bin/bash

GP2C_OPTS=""
GP2C="`pwd`/../gp2c $GP2C_OPTS"
ISO="`pwd`/../IsoChecker"


failure () {
	echo -e "\t\e[31mfailure\e[0m"
}

success () {
	echo -e "\t\e[success\e[0m"
}

for d in */ ; do
	p=${d%%/}
	pushd $d > /dev/null
	for t in *.host ; do
		echo -n Testing $t in $d
		( $GP2C $p.gp2 $t && ./$p > /tmp/$p.out && $ISO /tmp/$p.out Solutions/$t ) > /dev/null 2>&1 && success || failure
	done
	rm -f $p $p.c
	popd > /dev/null
done

