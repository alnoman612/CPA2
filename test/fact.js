
function fact(n) {
	var a = 1;
	
	if (n > 1) a = fact(n-1);
	
	return n * a;
}

var x = fact(10);  

var y = fact(y); 