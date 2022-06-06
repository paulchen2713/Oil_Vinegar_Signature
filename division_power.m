%
% division of numbers with power represenataion
% alpha^n1/alpha^n2
%
function n=division_power(n1,n2)
global m;
two_m=2^m;
two_m_1=two_m-1;
one=two_m_1;
zero=two_m;
if n2==one
    n=n1;
elseif n1==zero
    n=n1;
else
    n=mod(n1-n2,two_m_1);
    if n==0
        n=one;
    end
end
return


