//---------------------------Sort Algorithm-------------------------------------//
module sort;
    // Declare dynamic array
    bit [9:0] dynamic_array[];
    bit [9:0] sort_method[];
    bit [9:0] tmp_sort;
    initial begin
        dynamic_array = new[10];
        sort_method = new[10];
        foreach(dynamic_array[i]) begin
            dynamic_array[i] = $random % 256;
        end
        sort_method = dynamic_array;
        $display("-------------Before Sorting-------------");
        foreach(dynamic_array[i]) begin
            $display("dynamic_array[%0d]: %d", i, dynamic_array[i]);
        end

        // Sort method
        $display("-------------After Using Sorting Algorithm-------------"); 
        foreach(dynamic_array[i]) begin
            foreach(dynamic_array[j]) begin
                if(dynamic_array[i] < dynamic_array[j]) begin
                    tmp_sort = dynamic_array[i];
                    dynamic_array[i] = dynamic_array[j];
                    dynamic_array[j] = tmp_sort;
                end
            end
        end
        foreach(dynamic_array[i]) begin
            $display("dynamic_array[%0d]: %d", i, dynamic_array[i]);
        end


        // Predefined sort method
        sort_method.sort();
        $display("-------------After using Sort Method-------------");
        foreach(sort_method[i]) begin
            $display("sort_method[%0d]: %d", i, sort_method[i]);
        end

        // Compare the result
        $display("-----------------Compare the result-----------------");
        if(dynamic_array == sort_method) begin
            $display("The result is the same");
        end
        else begin
            $display("The result is different");
        end
    end
endmodule