function fact(n) {
	var ret = 1;
	while(n > 1) {
		if (ret > 1000) break;
		ret = ret * n;
		n = n - 1; 
	}
	return ret;
}

var x = fact(3);  

fact(x) 