//-------------------------------Function two include two more arguments min_limit and max_limit-------------------------------//
module function_array;
    typedef byte dynamic_array_t[];
    dynamic_array_t dynamic_array;
    byte queue[$];

  function dynamic_array_t dynamic_array_to_queue(input dynamic_array_t dynamic_array,
                                                  input byte min_limit = 0,
                                                  input byte max_limit = 256);
    byte queue[$];

    for
    
    return queue;
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

        // Testing default values
        $display("-------------Queue-------------");
        queue = dynamic_array_to_queue(dynamic_array);
        foreach(queue[i]) begin
            $display("queue[%0d]: %h", i, queue[i]);
        end


        // Testing min_limit and max_limit
        $display("-------------Queue with  min_limit and max_limit-------------");
        queue = dynamic_array_to_queue(dynamic_array, .min_limit(5), .max_limit(15));
        foreach(queue[i]) begin
            $display("queue[%0d]: %h", i, queue[i]);
        end


        // Testing max_limit is higher than the size of dynamic_array
        $display("-------------Queue with max_limit is higher than the size of dynamic_array-------------");
        queue = dynamic_array_to_queue(dynamic_array, .min_limit(2), .max_limit(30));
        foreach(queue[i]) begin
            $display("queue[%0d]: %h", i, queue[i]);
        end


        // Testing min_limit is lower than 0
        $display("-------------Queue with min_limit is lower than 0-------------");
        queue = dynamic_array_to_queue(dynamic_array, .min_limit(-5), .max_limit(15));
        foreach(queue[i]) begin
            $display("queue[%0d]: %h", i, queue[i]);
        end


        // Testing min_limit is higher than max_limit
        $display("-------------Queue with min_limit is higher than max_limit-------------");
        queue = dynamic_array_to_queue(dynamic_array, .min_limit(15), .max_limit(5));
        foreach(queue[i]) begin
            $display("queue[%0d]: %h", i, queue[i]);
        end

      
      	$finish;
    end

    
endmodule