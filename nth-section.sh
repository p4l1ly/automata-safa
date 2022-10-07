awk -vn=$1 'n<=0;/@/{--n}' | sed '/^@/Q'
