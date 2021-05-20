
function fact(n) {
	if (n <= 1) {
		return 1;
	}
	else {
		return n*fact(n-1);
	}
}

var x = fact(3);  

fact(x) 