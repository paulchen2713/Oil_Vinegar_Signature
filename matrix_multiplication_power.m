%
% matrix multiplication over power representation
%
function out=matrix_multiplication_power(A,B)
global m;
zero=2^m;
Ax=size(A,1);
By=size(B,2);
kk=size(A,2);
AB=zeros(Ax,By);
for ir=1:Ax
    for ic=1:By
        sum=zero;
        for ik=1:kk
            ab=multiplication_power(A(ir,ik),B(ik,ic));
            sum=addition_power(sum,ab);
        end
        AB(ir,ic)=sum;
    end
end
out=AB;
return