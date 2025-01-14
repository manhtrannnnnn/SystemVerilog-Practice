//----------------------------------------Class - OOP----------------------------------------//
    class packet #(parameter type DATA_TYPE = int);
        // Declare
        DATA_TYPE length;
        DATA_TYPE saddr;
        DATA_TYPE daddr;
        DATA_TYPE [length-1:0] data[];

        task random();
            this.data = new[this.length](data);
            foreach(this.data[i]) begin
                data[i] = $random;
            end
        endtask

        function void set_addr(DATA_TYPE saddr, DATA_TYPE daddr);
            this.saddr = saddr;
            this.daddr = daddr;
            while(this.saddr == this.daddr) begin
                this.daddr = $random;
            end
        endfunction

        function new();
            this.length = 10;
        endfunction

        function void display();
            $display("Length: %b, Source Address: %b, Destination Address: %b, Data: %p", this.length, this.saddr, this.daddr, this.data);
        endfunction
    endclass

    module exe1;
        parameter type DATA_TYPE = unsigned int;

      	packet #(.DATA_TYPE(DATA_TYPE)) pkg = new();
        initial begin
            pkg.random();
            pkg.display();
        end
    endmodule