//-------------------------------Function two include two more arguments min_limit and max_limit-------------------------------//
class packet;
    randc byte val;
endclass

module function_array;
    typedef byte dynamic_array_t[];
    dynamic_array_t dynamic_array;
    byte queue[$];

  function dynamic_array_t dynamic_array_to_queue(input dynamic_array_t dynamic_array,
                                                  input byte min_limit = -128,
                                                  input byte max_limit = 127);
    byte queue[$];
    foreach(dynamic_array[i]) begin
        if(dynamic_array[i] >= min_limit && dynamic_array[i] <= max_limit) begin
            queue.push_back(dynamic_array[i]);
        end
    end
    return queue;
  endfunction

    initial begin
        packet pkg = new();
        dynamic_array = new[20];
        foreach(dynamic_array[i]) begin
            if(pkg.randomize())
            dynamic_array[i] = pkg.val;
        end
        $display("-------------Dynamic Array-------------");
        foreach(dynamic_array[i]) begin
            $display("dynamic_array[%0d]: %d", i, dynamic_array[i]);
        end

        // Testing default values
        $display("-------------Queue-------------");
        queue = dynamic_array_to_queue(dynamic_array);
        #10;
        foreach(queue[i]) begin
            $display("queue[%0d]: %d", i, queue[i]);
        end


        // Testing min_limit and max_limit
        $display("-------------Queue with  min_limit(-20) and max_limit(20)-------------");
        queue = dynamic_array_to_queue(dynamic_array, .min_limit(-20), .max_limit(20));
        #10;
        foreach(queue[i]) begin
            $display("queue[%0d]: %d", i, queue[i]);
        end

        // Testing set only min_limit
        $display("-------------Queue with setting only min limit(10)-------------");
        queue = dynamic_array_to_queue(dynamic_array, .min_limit(20));
        #10;
        foreach(queue[i]) begin
            $display("queue[%0d]: %d", i, queue[i]);
        end

        // Testing set only max_limit
        $display("-------------Queue with setting only max limit(40)-------------");
        queue = dynamic_array_to_queue(dynamic_array, .max_limit(40));
        #10;
        foreach(queue[i]) begin
            $display("queue[%0d]: %d", i, queue[i]);
        end

        // Testing min_limit is higher than max_limit
        $display("-------------Queue with max_limit(-30) is higher than min_limit(100)-------------");
        queue = dynamic_array_to_queue(dynamic_array, .min_limit(100), .max_limit(-30));
        #10;
        foreach(queue[i]) begin
            $display("queue[%0d]: %d", i, queue[i]);
        end

      	$finish;
    end
endmodule