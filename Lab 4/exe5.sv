//----------------------------------------Parameterized Counter----------------------------------------//
module parameterized_counter #(
    parameter MAX_COUNTER = 7,
    parameter type DATA_TYPE = int,
    parameter step = 1
)(
    input clk, rst_n,
    input en, load,
    input DATA_TYPE  data_in,
    output DATA_TYPE counter
);
    always_ff @(posedge clk) begin
        if(!rst_n) begin
            counter <= 0;
        end
        else begin
            if(load) begin
                if(data_in % step == 0) begin
                    if(data_in < MAX_COUNTER) begin
                    counter <= data_in;
                    end
                    else begin
                        counter <= 0;
                    end
                end
                else begin
                    counter <= 0;
                end
            end
            else if(en && counter < MAX_COUNTER) begin
                counter <= counter + step;
            end
            else if(en && counter >= MAX_COUNTER) begin
                counter <= 0;
            end
        end
    end
endmodule


//----------------------------------------Verify with Month(Jan to July)----------------------------------------//
module parameterized_counter_tb;
    // Parameter
    parameter MAX_COUNTER = 7;
    parameter type DATA_TYPE = int;

    // Inputs
    logic clk, rst_n, en, load;
    DATA_TYPE data_in;

    // Outputs
    DATA_TYPE counter;

    // Instantiate the Unit Under Test (UUT)
    parameterized_counter #(
        .MAX_COUNTER(MAX_COUNTER),
        .DATA_TYPE(DATA_TYPE)
    ) uut (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .load(load),
        .data_in(data_in),
        .counter(counter)
    );

    // Test stimulus
    initial begin
        rst_n = 1'b0; load = 1'b0; en = 1'b0; data_in = 1'b0; #10;

        // Reset
        $display("-------------------------Normal Flow-------------------------");
        rst_n = 1'b1; en = 1'b1; #200;

        // Testing Load
        $display("-------------------------Load-------------------------");
        load = 1'b1; data_in = 3; #10;
        load  = 1'b0; #200;

        // Test invalid data
        $display("-------------------------Invalid Data-------------------------");
        load = 1'b1; data_in = 10; #10;
        load = 1'b0; #200;

        // Testing enable
        $display("-------------------------Enable-------------------------");
        en = 1'b0; #200;

        // Testing Reset
        $display("-------------------------Reset-------------------------");
        rst_n = 1'b0; #200;
        $finish;
    end

    // Monitor
    initial begin
        $monitor("[Time: %0t] Reset: %b, Load: %b, Enable: %b, Data In: %0d ||Counter: %0d", $time, rst_n, load, en, data_in, counter);
    end

    // Generate Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Generate Waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end
endmodule


//----------------------------------------Verify with Mod 7 counter made of bits----------------------------------------//
module parameterized_counter_tb;
    // Parameter
    parameter MAX_COUNTER = 7;
    parameter type DATA_TYPE = bit[2:0];

    // Inputs
    logic clk, rst_n, en, load;
    DATA_TYPE data_in;

    // Outputs
    DATA_TYPE counter;

    // Instantiate the Unit Under Test (UUT)
    parameterized_counter #(
        .MAX_COUNTER(MAX_COUNTER),
        .DATA_TYPE(DATA_TYPE)
    ) uut (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .load(load),
        .data_in(data_in),
        .counter(counter)
    );

    // Test stimulus
    initial begin
        rst_n = 1'b0; load = 1'b0; en = 1'b0; data_in = 1'b0; #10;

        // Reset
        $display("-------------------------Normal Flow-------------------------");
        rst_n = 1'b1; en = 1'b1; #200;

        // Testing Load
        $display("-------------------------Load-------------------------");
        load = 1'b1; data_in = 3; #10;
        load  = 1'b0; #200;

        // Test invalid data
        $display("-------------------------Invalid Data-------------------------");
        load = 1'b1; data_in = 10; #10;
        load = 1'b0; #200;

        // Testing enable
        $display("-------------------------Enable-------------------------");
        en = 1'b0; #200;

        // Testing Reset
        $display("-------------------------Reset-------------------------");
        rst_n = 1'b0; #200;
        $finish;
    end

    // Monitor
    initial begin
        $monitor("[Time: %0t] Reset: %b, Load: %b, Enable: %b, Data In: %0d ||Counter: %0d", $time, rst_n, load, en, data_in, counter);
    end

    // Generate Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Generate Waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end
endmodule   



//----------------------------------------Verify with Even til 30----------------------------------------//
module parameterized_counter_tb;
    // Parameter
    parameter MAX_COUNTER = 30;
    parameter type DATA_TYPE = int;
  	parameter step = 2;

    // Inputs
    logic clk, rst_n, en, load;
    DATA_TYPE data_in;

    // Outputs
    DATA_TYPE counter;

    // Instantiate the Unit Under Test (UUT)
    parameterized_counter #(
        .MAX_COUNTER(MAX_COUNTER),
        .DATA_TYPE(DATA_TYPE),
        .step(step)
    ) uut (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .load(load),
        .data_in(data_in),
        .counter(counter)
    );

    // Test stimulus
    initial begin
        rst_n = 1'b0; load = 1'b0; en = 1'b0; data_in = 1'b0; #10;

        // Reset
        $display("-------------------------Normal Flow-------------------------");
        rst_n = 1'b1; en = 1'b1; #400;

        // Testing Load
        $display("-------------------------Load-------------------------");
        load = 1'b1; data_in = 8; #10;
        load  = 1'b0; #300;

        // Test invalid data
        $display("-------------------------Invalid Data (Out of MAX COUNTER)-------------------------");
        load = 1'b1; data_in = 10; #10;
        load = 1'b0; #300;

        // Test invalid data
        $display("-------------------------Invalid Data (Not even number)-------------------------");
        load = 1'b1; data_in = 15; #10;
        load = 1'b0; #300;

        // Testing enable
        $display("-------------------------Enable-------------------------");
        en = 1'b0; #50;

        // Testing Reset
        $display("-------------------------Reset-------------------------");
        rst_n = 1'b0; #50;
        $finish;
    end

    // Monitor
    initial begin
        $monitor("[Time: %0t] Reset: %b, Load: %b, Enable: %b, Data In: %0d ||Counter: %0d", $time, rst_n, load, en, data_in, counter);
    end

    // Generate Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Generate Waveform
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end
endmodule   




