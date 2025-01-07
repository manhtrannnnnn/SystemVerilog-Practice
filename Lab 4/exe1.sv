//------------------------------- Function that accepts a 1-D array of bytes and returns a queue of bytes -------------------------------//

module function_array;
    typedef byte dynamic_array_t[];
    dynamic_array_t dynamic_array;
    byte queue[$];

  function dynamic_array_t dynamic_array_to_queue(input dynamic_array_t dynamic_array_tmp);
        automatic byte queue_tmp[$];
        int i;
        foreach(dynamic_array_tmp[i]) begin
            queue_tmp.push_back(dynamic_array_tmp[i]);
        end
        return queue_tmp;
    endfunction

    initial begin
        dynamic_array = new[20];
        foreach(dynamic_array[i]) begin
            dynamic_array[i] = $random % 256;
        end
        $display("-------------Dynamic Array-------------");
        foreach(dynamic_array[i]) begin
            $display("dynamic_array[%0d]: %h", i, dynamic_array[i]);
        end
        queue = dynamic_array_to_queue(dynamic_array);
        $display("-------------Queue-------------");
        foreach(queue[i]) begin
            $display("queue[%0d]: %h", i, queue[i]);
        end
      
      	$finish;
    end


endmodule