%
% addition of numbers with power representation
%
function n=addition_power(n1,n2)
global alpha alpha1;
nc=bitxor(alpha(n1,:),alpha(n2,:));
n=alpha1(bin2dec(char(nc+48))+1);
return

