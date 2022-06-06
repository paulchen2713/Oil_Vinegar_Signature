%
% reduced row echelon form of a binary matrix
%
function out=reduced_row_echelon_form_power(A)
global m;
zero=2^m;
n=size(A,1);
for ix=1:n-1
    i=ix;
    while A(i,ix)==zero
        i=i+1;
    end
    if i~=ix
        temp=A(ix,:);
        A(ix,:)=A(i,:);
        A(i,:)=temp;   
    end
    dd=A(ix,ix);
    for in=1:2*n
        A(ix,in)=division_power(A(ix,in),dd);
    end
    for ii=ix+1:n
        if A(ii,ix)~=zero
            dd=A(ii,ix);
            for in=1:2*n
                A(ii,in)=division_power(A(ii,in),dd);
                A(ii,in)=addition_power(A(ii,in),A(ix,in));
            end
        end
    end
end
dd=A(n,n);
for in=1:2*n
    A(n,in)=division_power(A(n,in),dd);
end
for ix=1:n-1
    for i=n-ix:-1:1
        if A(i,n+1-ix)~=zero
            temp=A(n+1-ix,:);
            dd=A(i,n+1-ix);
            for in=1:2*n
                temp(in)=multiplication_power(temp(in),dd);
                A(i,in)=addition_power(A(i,in),temp(in));
            end
        end
    end
end
out=A;
return


