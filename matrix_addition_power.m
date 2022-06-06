%
% matrix addition of numbers with power representation
%
function out=matrix_addition_power(A,B)
global m;
zero=2^m;
Ax=size(A,1);
Ay=size(A,2);
AB=zero*ones(Ax,Ay);
for ir=1:Ax
    for ic=1:Ay
        AB(ir,ic)=addition_power(A(ir,ic),B(ir,ic));
    end
end
out=AB;
return
