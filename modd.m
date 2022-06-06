%
%
%
function out=modd(i)
out=mod(i,8);
if out==0
    out=8;
end
return