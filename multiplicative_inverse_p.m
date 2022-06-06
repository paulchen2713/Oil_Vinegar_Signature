%
% multiplicative inverse for positive integer p
%
function [d,x]=multiplicative_inverse_p(a,p)
u=a;
v=p;
x1=1;
y1=0;
x2=0;
y2=1;
while u~=0
    qq=floor(v/u);
    r=v-qq*u;
    x=x2-qq*x1;
    y=y2-qq*y1;
    v=u;
    u=r;
    x2=x1;
    x1=x;
    y2=y1;
    y1=y;
end
d=v;
x=x2;
if x<0
    x=mod(x,p);
end
return