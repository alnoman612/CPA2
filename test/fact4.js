function fact(n) {
	var ret = 1;
	while(n > 1) {
		if (ret > 1000) break;
		n = n - 1;
		if (n % 2 == 0) continue;
		ret = ret * n;
	}
	return ret;
}

var x = fact(3);  

fact(x) 