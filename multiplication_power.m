%
% multiplication of numbers with power representation
%
function n=multiplication_power(n1,n2)
global m;
two_m=2^m;
two_m_1=two_m-1;
one=two_m_1;
zero=two_m;
if n1==zero || n2==zero
    n=zero;
else
    n=mod(n1+n2,two_m_1);
    if n==0
        n=one;
    end
end
return
